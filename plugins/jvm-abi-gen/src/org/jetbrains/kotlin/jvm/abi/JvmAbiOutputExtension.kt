/*
 * Copyright 2010-2020 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.jvm.abi

import org.jetbrains.kotlin.backend.common.output.OutputFile
import org.jetbrains.kotlin.backend.common.output.OutputFileCollection
import org.jetbrains.kotlin.backend.common.output.SimpleOutputBinaryFile
import org.jetbrains.kotlin.cli.common.messages.MessageCollector
import org.jetbrains.kotlin.cli.common.output.writeAllTo
import org.jetbrains.kotlin.cli.jvm.compiler.CompileEnvironmentUtil
import org.jetbrains.kotlin.codegen.ClassFileFactory
import org.jetbrains.kotlin.codegen.extensions.ClassFileFactoryFinalizerExtension
import org.jetbrains.kotlin.load.java.JvmAnnotationNames
import org.jetbrains.org.objectweb.asm.*
import org.jetbrains.org.objectweb.asm.commons.ClassRemapper
import org.jetbrains.org.objectweb.asm.commons.Remapper
import org.jetbrains.org.objectweb.asm.tree.FieldNode
import org.jetbrains.org.objectweb.asm.tree.MethodNode
import java.io.File

class JvmAbiOutputExtension(
    private val outputPath: File,
    private val abiClassInfos: Map<String, AbiClassInfo>,
    private val messageCollector: MessageCollector,
    private val deleteNonPublicAbi: Boolean,
) : ClassFileFactoryFinalizerExtension {
    override fun finalizeClassFactory(factory: ClassFileFactory) {
        // We need to wait until the end to produce any output in order to strip classes
        // from the InnerClasses attributes.
        val outputFiles = AbiOutputFiles(abiClassInfos, factory, deleteNonPublicAbi)
        if (outputPath.extension == "jar") {
            // We don't include the runtime or main class in interface jars and always reset time stamps.
            CompileEnvironmentUtil.writeToJar(
                outputPath,
                false,
                true,
                true,
                null,
                outputFiles,
                messageCollector
            )
        } else {
            outputFiles.writeAllTo(outputPath)
        }
    }

    private class InnerClassInfo(val name: String, val outerName: String?, val innerName: String?, val access: Int)

    private class AbiOutputFiles(
        private val abiClassInfos: Map<String, AbiClassInfo>,
        private val outputFiles: OutputFileCollection,
        private val deleteNonPublicAbi: Boolean
    ) : OutputFileCollection {
        override fun get(relativePath: String): OutputFile? {
            error("AbiOutputFiles does not implement `get`.")
        }

        override fun asList(): List<OutputFile> {
            val metadata = outputFiles.asList().filter {
                !it.relativePath.endsWith(".class")
            }.sortedBy { it.relativePath }

            val classFiles = abiClassInfos.keys.sorted().mapNotNull { internalName ->
                // Note that outputFile may be null, e.g., for empty $DefaultImpls classes in the JVM backend.
                val outputFile = outputFiles.get("$internalName.class") ?: return@mapNotNull null
                when (val abiInfo = abiClassInfos.getValue(internalName)) {
                    is AbiClassInfo.Delete -> null
                    is AbiClassInfo.Keep -> outputFile // Copy verbatim
                    is AbiClassInfo.Strip -> {
                        val memberInfo = abiInfo.memberInfo
                        val innerClassesToKeep = mutableSetOf<String>()
                        val writer = ClassWriter(0)
                        val remapper = ClassRemapper(writer, object : Remapper() {
                            override fun map(internalName: String): String =
                                internalName.also { innerClassesToKeep.add(it) }
                        })
                        ClassReader(outputFile.asByteArray()).accept(object : ClassVisitor(Opcodes.API_VERSION, remapper) {
                            private var infoGatheringPass = true

                            private val keptFields = mutableListOf<FieldNode>()
                            private val keptMethods = mutableListOf<MethodNode>()

                            private val innerClassInfos = mutableMapOf<String, InnerClassInfo>()

                            override fun visitField(
                                access: Int,
                                name: String?,
                                descriptor: String?,
                                signature: String?,
                                value: Any?,
                            ): FieldVisitor? {
                                return if (infoGatheringPass) {
                                    if (memberInfo[Member(name, descriptor)] == AbiMemberInfo.KEEP) {
                                        FieldNode(access, name, descriptor, signature, value).also {
                                            keptFields += it
                                        }
                                    } else {
                                        null //remove
                                    }
                                } else {
                                    super.visitField(access, name, descriptor, signature, value)
                                }
                            }

                            override fun visitMethod(
                                access: Int,
                                name: String,
                                descriptor: String,
                                signature: String?,
                                exceptions: Array<out String>?
                            ): MethodVisitor? {
                                val info = memberInfo[Member(name, descriptor)]

                                return if (infoGatheringPass) {
                                    if (info != null) {
                                        MethodNode(access, name, descriptor, signature, exceptions).also {
                                            keptMethods += it
                                        }
                                    } else {
                                        null //remove
                                    }
                                } else {
                                    val visitor = super.visitMethod(access, name, descriptor, signature, exceptions)
                                    if (info == AbiMemberInfo.STRIP) StrippingMethodVisitor(visitor) else visitor
                                }
                            }

                            // Strip source debug extensions if there are no inline functions.
                            override fun visitSource(source: String?, debug: String?) {
                                // TODO Normalize and strip unused line numbers from SourceDebugExtensions
                                if (memberInfo.values.any { it == AbiMemberInfo.KEEP }) {
                                    super.visitSource(source, debug)
                                } else {
                                    super.visitSource(source, null)
                                }
                            }

                            // Remove inner classes which are not present in the abi jar.
                            override fun visitInnerClass(name: String, outerName: String?, innerName: String?, access: Int) {
                                // `visitInnerClass` is called before `visitField`/`visitMethod`, so we don't know
                                // which types are referenced by kept methods yet.
                                innerClassInfos[name] = InnerClassInfo(name, outerName, innerName, access)
                            }

                            // Strip private declarations from the Kotlin Metadata annotation.
                            override fun visitAnnotation(descriptor: String?, visible: Boolean): AnnotationVisitor? {
                                if (deleteNonPublicAbi && descriptor == JvmAnnotationNames.SOURCE_DEBUG_EXTENSION_DESC) return null
                                val delegate = super.visitAnnotation(descriptor, visible)
                                if (descriptor != JvmAnnotationNames.METADATA_DESC)
                                    return delegate

                                val classesToBeDeleted = abiClassInfos.mapNotNullTo(mutableSetOf()) { (className, action) ->
                                    className.takeIf { action == AbiClassInfo.Delete }
                                }

                                return abiMetadataProcessor(delegate, classesToBeDeleted, deleteNonPublicAbi)
                            }

                            override fun visitEnd() {
                                infoGatheringPass = false
                                keptFields
                                    .sortedBy { it.name }
                                    .forEach { it.accept(this) }
                                keptMethods
                                    .sortedBy { it.name }
                                    .forEach { it.accept(this) }

                                innerClassesToKeep.addInnerClasses(innerClassInfos, internalName)
                                innerClassesToKeep.addOuterClasses(innerClassInfos)

                                // Output classes in sorted order so that changes in original ordering due to method bodies, etc.
                                // don't affect the ABI JAR.
                                for (name in innerClassesToKeep.sorted()) {
                                    innerClassInfos[name]?.let { super.visitInnerClass(it.name, it.outerName, it.innerName, it.access) }
                                }

                                super.visitEnd()
                            }
                        }, 0)
                        SimpleOutputBinaryFile(outputFile.sourceFiles, outputFile.relativePath, writer.toByteArray())
                    }
                }
            }

            return metadata + classFiles
        }

        // Outer class infos for a class and all classes transitively nested in it (that are public ABI)
        // should be kept in its own class file even if the classes are otherwise unused.
        private fun MutableSet<String>.addInnerClasses(innerClassInfos: Map<String, InnerClassInfo>, internalName: String) {
            val innerClassesByOuterName = innerClassInfos.values.groupBy { it.outerName }
            val stack = mutableListOf(internalName)
            while (stack.isNotEmpty()) {
                val next = stack.removeLast()
                add(next)
                // Classes form a tree by nesting, so none of the children have been visited yet.
                innerClassesByOuterName[next]?.mapNotNullTo(stack) { info ->
                    info.name.takeIf { abiClassInfos[it] != AbiClassInfo.Delete }
                }
            }
        }

        // For every class A.B, if its outer class info is kept then so should be A's.
        private fun MutableSet<String>.addOuterClasses(innerClassInfos: Map<String, InnerClassInfo>) {
            for (name in toList()) {
                var info = innerClassInfos[name]
                while (info != null) {
                    info = info.outerName?.takeIf(::add)?.let(innerClassInfos::get)
                }
            }
        }
    }

    private class StrippingMethodVisitor(visitor: MethodVisitor?): MethodVisitor(Opcodes.API_VERSION, visitor) {
        override fun visitCode() {
            with(mv) {
                visitCode()
                visitInsn(Opcodes.ACONST_NULL)
                visitInsn(Opcodes.ATHROW)
                visitMaxs(0, 0)
                visitEnd()
            }
            // Only instructions and locals follow after `visitCode`.
            mv = null
        }
    }
}
