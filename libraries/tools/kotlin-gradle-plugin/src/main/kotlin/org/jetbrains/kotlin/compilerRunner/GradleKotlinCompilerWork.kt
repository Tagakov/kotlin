/*
 * Copyright 2010-2018 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.compilerRunner

import org.gradle.api.logging.Logger
import org.jetbrains.kotlin.build.report.metrics.*
import org.jetbrains.kotlin.cli.common.CompilerSystemProperties
import org.jetbrains.kotlin.cli.common.CompilerSystemProperties.COMPILE_INCREMENTAL_WITH_CLASSPATH_SNAPSHOTS
import org.jetbrains.kotlin.cli.common.ExitCode
import org.jetbrains.kotlin.cli.common.messages.MessageCollector
import org.jetbrains.kotlin.cli.common.toBooleanLenient
import org.jetbrains.kotlin.config.Services
import org.jetbrains.kotlin.daemon.common.*
import org.jetbrains.kotlin.gradle.logging.*
import org.jetbrains.kotlin.gradle.plugin.internal.state.TaskExecutionResults
import org.jetbrains.kotlin.gradle.plugin.internal.state.TaskLoggers
import org.jetbrains.kotlin.gradle.report.*
import org.jetbrains.kotlin.gradle.report.TaskExecutionInfo
import org.jetbrains.kotlin.gradle.report.TaskExecutionProperties.ABI_SNAPSHOT
import org.jetbrains.kotlin.gradle.report.TaskExecutionResult
import org.jetbrains.kotlin.gradle.tasks.clearLocalState
import org.jetbrains.kotlin.gradle.tasks.throwGradleExceptionIfError
import org.jetbrains.kotlin.gradle.utils.stackTraceAsString
import org.jetbrains.kotlin.incremental.ChangedFiles
import org.jetbrains.kotlin.incremental.IncrementalModuleInfo
import org.slf4j.LoggerFactory
import java.io.*
import java.net.URLClassLoader
import java.rmi.RemoteException
import java.util.*
import java.util.concurrent.Callable
import java.util.concurrent.Executors
import javax.inject.Inject
import kotlin.collections.ArrayList

internal class ProjectFilesForCompilation(
    val projectRootFile: File,
    val clientIsAliveFlagFile: File,
    val sessionFlagFile: File,
    val buildDir: File
) : Serializable {
    //TODO
    constructor(logger: Logger, projectDir:File, buildDir: File, prjectName: String, projectRootDir: File, sessionDir: File) : this(
        projectRootFile = projectDir,
        clientIsAliveFlagFile = GradleCompilerRunner.getOrCreateClientFlagFile(logger, prjectName),
        sessionFlagFile = GradleCompilerRunner.getOrCreateSessionFlagFile(logger, sessionDir, projectRootDir),
        buildDir = buildDir
    )

    companion object {
        const val serialVersionUID: Long = 0
    }
}

internal class GradleKotlinCompilerWorkArguments(
    val projectFiles: ProjectFilesForCompilation,
    val compilerFullClasspath: List<File>,
    val compilerClassName: String,
    val compilerArgs: Array<String>,
    val isVerbose: Boolean,
    val incrementalCompilationEnvironment: IncrementalCompilationEnvironment?,
    val incrementalModuleInfo: IncrementalModuleInfo?,
    val outputFiles: List<File>,
    val taskPath: String,
    val reportingSettings: ReportingSettings,
    val kotlinScriptExtensions: Array<String>,
    val allWarningsAsErrors: Boolean,
    val daemonJvmArgs: List<String>?
) : Serializable {
    companion object {
        const val serialVersionUID: Long = 0
    }
}

internal class GradleKotlinCompilerWork @Inject constructor(
    /**
     * Arguments are passed through [GradleKotlinCompilerWorkArguments],
     * because Gradle Workers API does not support nullable arguments (https://github.com/gradle/gradle/issues/2405),
     * and because Workers API does not support named arguments,
     * which are useful when there are many arguments with the same type
     * (to protect against parameters reordering bugs)
     */
    config: GradleKotlinCompilerWorkArguments
) : Runnable {

    companion object {
        init {
            if (System.getProperty("org.jetbrains.kotlin.compilerRunner.GradleKotlinCompilerWork.trace.loading") == "true") {
                println("Loaded GradleKotlinCompilerWork")
            }
        }
    }

    private val projectRootFile = config.projectFiles.projectRootFile
    private val clientIsAliveFlagFile = config.projectFiles.clientIsAliveFlagFile
    private val sessionFlagFile = config.projectFiles.sessionFlagFile
    private val compilerFullClasspath = config.compilerFullClasspath
    private val compilerClassName = config.compilerClassName
    private val compilerArgs = config.compilerArgs
    private val isVerbose = config.isVerbose
    private val incrementalCompilationEnvironment = config.incrementalCompilationEnvironment
    private val incrementalModuleInfo = config.incrementalModuleInfo
    private val outputFiles = config.outputFiles
    private val taskPath = config.taskPath
    private val reportingSettings = config.reportingSettings
    private val kotlinScriptExtensions = config.kotlinScriptExtensions
    private val allWarningsAsErrors = config.allWarningsAsErrors
    private val buildDir = config.projectFiles.buildDir
    private val metrics = if (reportingSettings.reportMetrics) BuildMetricsReporterImpl() else DoNothingBuildMetricsReporter
    private var icLogLines: List<String> = emptyList()
    private val daemonJvmArgs = config.daemonJvmArgs

    private val log: KotlinLogger =
        TaskLoggers.get(taskPath)?.let { GradleKotlinLogger(it).apply { debug("Using '$taskPath' logger") } }
            ?: run {
                val logger = LoggerFactory.getLogger("GradleKotlinCompilerWork")
                val kotlinLogger = if (logger is org.gradle.api.logging.Logger) {
                    GradleKotlinLogger(logger)
                } else SL4JKotlinLogger(logger)

                kotlinLogger.apply {
                    debug("Could not get logger for '$taskPath'. Falling back to sl4j logger")
                }
            }

    private val isIncremental: Boolean
        get() = incrementalCompilationEnvironment != null

    override fun run() {
        try {
            val messageCollector = GradlePrintingMessageCollector(log, allWarningsAsErrors)
            val exitCode = compileWithDaemonOrFallbackImpl(messageCollector)
            if (incrementalCompilationEnvironment?.disableMultiModuleIC == true) {
                incrementalCompilationEnvironment.multiModuleICSettings.buildHistoryFile.delete()
            }

            throwGradleExceptionIfError(exitCode)
        } finally {
            val properties = ArrayList<TaskExecutionProperties>()
            COMPILE_INCREMENTAL_WITH_CLASSPATH_SNAPSHOTS.value.toBooleanLenient()?.let {
                if (it) properties.add(ABI_SNAPSHOT)
            }
            CompilerSystemProperties.COMPILE_INCREMENTAL_WITH_ARTIFACT_TRANSFORM.value.toBooleanLenient()?.let {
                if (it) properties.add(TaskExecutionProperties.ARTIFACT_TRANSFORM)
            }

            val taskInfo = TaskExecutionInfo(
                changedFiles = incrementalCompilationEnvironment?.changedFiles,
                properties = properties
            )
            val result = TaskExecutionResult(buildMetrics = metrics.getMetrics(), icLogLines = icLogLines, taskInfo = taskInfo)
            TaskExecutionResults[taskPath] = result
        }
    }

    private fun compileWithDaemonOrFallbackImpl(messageCollector: MessageCollector): ExitCode {
        with(log) {
            kotlinDebug { "Kotlin compiler class: ${compilerClassName}" }
            kotlinDebug { "Kotlin compiler classpath: ${compilerFullClasspath.joinToString { it.canonicalPath }}" }
            kotlinDebug { "$taskPath Kotlin compiler args: ${compilerArgs.joinToString(" ")}" }
        }

        val executionStrategy = kotlinCompilerExecutionStrategy()
        if (executionStrategy == DAEMON_EXECUTION_STRATEGY) {
            val daemonExitCode = compileWithDaemon(messageCollector)

            if (daemonExitCode != null) {
                return daemonExitCode
            } else {
                log.warn("Could not connect to kotlin daemon. Using fallback strategy.")
            }
        }

        val isGradleDaemonUsed = System.getProperty("org.gradle.daemon")?.let(String::toBoolean)
        return if (executionStrategy == IN_PROCESS_EXECUTION_STRATEGY || isGradleDaemonUsed == false) {
            compileInProcess(messageCollector)
        } else {
            compileOutOfProcess()
        }
    }

    private fun compileWithDaemon(messageCollector: MessageCollector): ExitCode? {
        val isDebugEnabled = log.isDebugEnabled || System.getProperty("kotlin.daemon.debug.log")?.toBoolean() ?: true
        val daemonMessageCollector =
            if (isDebugEnabled) messageCollector else MessageCollector.NONE
        val connection =
            metrics.measure(BuildTime.CONNECT_TO_DAEMON) {
                try {
                    GradleCompilerRunner.getDaemonConnectionImpl(
                        clientIsAliveFlagFile,
                        sessionFlagFile,
                        compilerFullClasspath,
                        daemonMessageCollector,
                        isDebugEnabled = isDebugEnabled,
                        daemonJvmArgs = daemonJvmArgs
                    )
                } catch (e: Throwable) {
                    log.error("Caught an exception trying to connect to Kotlin Daemon:")
                    log.error(e.stackTraceAsString())
                    null
                }
            }
        if (connection == null) {
            if (isIncremental) {
                log.warn("Could not perform incremental compilation: $COULD_NOT_CONNECT_TO_DAEMON_MESSAGE")
            } else {
                log.warn(COULD_NOT_CONNECT_TO_DAEMON_MESSAGE)
            }
            return null
        }

        val (daemon, sessionId) = connection

        if (log.isDebugEnabled) {
            daemon.getDaemonJVMOptions().takeIf { it.isGood }?.let { jvmOpts ->
                log.debug("Kotlin compile daemon JVM options: ${jvmOpts.get().mappers.flatMap { it.toArgs("-") }}")
            }
        }
        val targetPlatform = when (compilerClassName) {
            KotlinCompilerClass.JVM -> CompileService.TargetPlatform.JVM
            KotlinCompilerClass.JS -> CompileService.TargetPlatform.JS
            KotlinCompilerClass.METADATA -> CompileService.TargetPlatform.METADATA
            else -> throw IllegalArgumentException("Unknown compiler type $compilerClassName")
        }
        val bufferingMessageCollector = GradleBufferingMessageCollector()
        val exitCode = try {
            val res = if (isIncremental) {
                incrementalCompilationWithDaemon(daemon, sessionId, targetPlatform, bufferingMessageCollector)
            } else {
                nonIncrementalCompilationWithDaemon(daemon, sessionId, targetPlatform, bufferingMessageCollector)
            }
            bufferingMessageCollector.flush(messageCollector)
            exitCodeFromProcessExitCode(log, res.get())
        } catch (e: Throwable) {
            bufferingMessageCollector.flush(messageCollector)
            log.error("Compilation with Kotlin compile daemon was not successful")
            log.error(e.stackTraceAsString())
            null
        }
        // todo: can we clear cache on the end of session?
        // often source of the NoSuchObjectException and UnmarshalException, probably caused by the failed/crashed/exited daemon
        // TODO: implement a proper logic to avoid remote calls in such cases
        try {
            metrics.measure(BuildTime.CLEAR_JAR_CACHE) {
                daemon.clearJarCache()
            }
        } catch (e: RemoteException) {
            log.warn("Unable to clear jar cache after compilation, maybe daemon is already down: $e")
        }
        log.logFinish(DAEMON_EXECUTION_STRATEGY)
        return exitCode
    }

    private fun nonIncrementalCompilationWithDaemon(
        daemon: CompileService,
        sessionId: Int,
        targetPlatform: CompileService.TargetPlatform,
        bufferingMessageCollector: GradleBufferingMessageCollector
    ): CompileService.CallResult<Int> {
        metrics.addAttribute(BuildAttribute.IC_IS_NOT_ENABLED)
        val compilationOptions = CompilationOptions(
            compilerMode = CompilerMode.NON_INCREMENTAL_COMPILER,
            targetPlatform = targetPlatform,
            reportCategories = reportCategories(isVerbose),
            reportSeverity = reportSeverity(isVerbose),
            requestedCompilationResults = emptyArray(),
            kotlinScriptExtensions = kotlinScriptExtensions
        )
        val servicesFacade = GradleCompilerServicesFacadeImpl(log, bufferingMessageCollector)
        return metrics.measure(BuildTime.NON_INCREMENTAL_COMPILATION_DAEMON) {
            daemon.compile(sessionId, compilerArgs, compilationOptions, servicesFacade, compilationResults = null)
        }
    }

    private fun incrementalCompilationWithDaemon(
        daemon: CompileService,
        sessionId: Int,
        targetPlatform: CompileService.TargetPlatform,
        bufferingMessageCollector: GradleBufferingMessageCollector
    ): CompileService.CallResult<Int> {
        val icEnv = incrementalCompilationEnvironment ?: error("incrementalCompilationEnvironment is null!")
        val knownChangedFiles = icEnv.changedFiles as? ChangedFiles.Known
        val requestedCompilationResults = requestedCompilationResults()
        val compilationOptions = IncrementalCompilationOptions(
            areFileChangesKnown = knownChangedFiles != null,
            modifiedFiles = knownChangedFiles?.modified,
            deletedFiles = knownChangedFiles?.removed,
            classpathChanges = icEnv.classpathChanges,
            workingDir = icEnv.workingDir,
            reportCategories = reportCategories(isVerbose),
            reportSeverity = reportSeverity(isVerbose),
            requestedCompilationResults = requestedCompilationResults.map { it.code }.toTypedArray(),
            compilerMode = CompilerMode.INCREMENTAL_COMPILER,
            targetPlatform = targetPlatform,
            usePreciseJavaTracking = icEnv.usePreciseJavaTracking,
            outputFiles = outputFiles,
            multiModuleICSettings = icEnv.multiModuleICSettings,
            modulesInfo = incrementalModuleInfo!!,
            kotlinScriptExtensions = kotlinScriptExtensions
        )

        log.info("Options for KOTLIN DAEMON: $compilationOptions")
        val servicesFacade = GradleIncrementalCompilerServicesFacadeImpl(log, bufferingMessageCollector)
        val compilationResults = GradleCompilationResults(log, projectRootFile)
        return metrics.measure(BuildTime.RUN_COMPILER) {
            daemon.compile(sessionId, compilerArgs, compilationOptions, servicesFacade, compilationResults)
        }.also {
            metrics.addMetrics(compilationResults.buildMetrics)
            icLogLines = compilationResults.icLogLines
        }
    }

    private fun compileOutOfProcess(): ExitCode {
        metrics.addAttribute(BuildAttribute.OUT_OF_PROCESS_EXECUTION)
        clearLocalState(outputFiles, log, metrics, reason = "out-of-process execution strategy is non-incremental")

        return metrics.measure(BuildTime.NON_INCREMENTAL_COMPILATION_OUT_OF_PROCESS) {
            runToolInSeparateProcess(compilerArgs, compilerClassName, compilerFullClasspath, log, buildDir)
        }
    }

    private fun compileInProcess(messageCollector: MessageCollector): ExitCode {
        metrics.addAttribute(BuildAttribute.IN_PROCESS_EXECUTION)
        clearLocalState(outputFiles, log, metrics, reason = "in-process execution strategy is non-incremental")

        metrics.startMeasure(BuildTime.NON_INCREMENTAL_COMPILATION_IN_PROCESS, System.nanoTime())
        // in-process compiler should always be run in a different thread
        // to avoid leaking thread locals from compiler (see KT-28037)
        val threadPool = Executors.newSingleThreadExecutor()
        val bufferingMessageCollector = GradleBufferingMessageCollector()
        return try {
            val future = threadPool.submit(Callable {
                compileInProcessImpl(bufferingMessageCollector)
            })
            future.get()
        } finally {
            bufferingMessageCollector.flush(messageCollector)
            threadPool.shutdown()

            metrics.endMeasure(BuildTime.NON_INCREMENTAL_COMPILATION_IN_PROCESS, System.nanoTime())
        }
    }

    private fun compileInProcessImpl(messageCollector: MessageCollector): ExitCode {
        val stream = ByteArrayOutputStream()
        val out = PrintStream(stream)
        // todo: cache classloader?
        val classLoader = URLClassLoader(compilerFullClasspath.map { it.toURI().toURL() }.toTypedArray())
        val servicesClass = Class.forName(Services::class.java.canonicalName, true, classLoader)
        val emptyServices = servicesClass.getField("EMPTY").get(servicesClass)
        val compiler = Class.forName(compilerClassName, true, classLoader)

        val exec = compiler.getMethod(
            "execAndOutputXml",
            PrintStream::class.java,
            servicesClass,
            Array<String>::class.java
        )

        val res = exec.invoke(compiler.newInstance(), out, emptyServices, compilerArgs)
        val exitCode = ExitCode.valueOf(res.toString())
        processCompilerOutput(
            messageCollector,
            OutputItemsCollectorImpl(),
            stream,
            exitCode
        )
        log.logFinish(IN_PROCESS_EXECUTION_STRATEGY)
        return exitCode
    }

    private fun requestedCompilationResults(): EnumSet<CompilationResultCategory> {
        val requestedCompilationResults = EnumSet.of(CompilationResultCategory.IC_COMPILE_ITERATION)
        when (reportingSettings.buildReportMode) {
            BuildReportMode.NONE -> null
            BuildReportMode.SIMPLE -> CompilationResultCategory.BUILD_REPORT_LINES
            BuildReportMode.VERBOSE -> CompilationResultCategory.VERBOSE_BUILD_REPORT_LINES
        }?.let { requestedCompilationResults.add(it) }
        if (reportingSettings.reportMetrics) {
            requestedCompilationResults.add(CompilationResultCategory.BUILD_METRICS)
        }
        return requestedCompilationResults
    }

    private fun reportCategories(verbose: Boolean): Array<Int> =
        if (!verbose) {
            arrayOf(ReportCategory.COMPILER_MESSAGE.code)
        } else {
            ReportCategory.values().map { it.code }.toTypedArray()
        }

    private fun reportSeverity(verbose: Boolean): Int =
        if (!verbose) {
            ReportSeverity.INFO.code
        } else {
            ReportSeverity.DEBUG.code
        }
}