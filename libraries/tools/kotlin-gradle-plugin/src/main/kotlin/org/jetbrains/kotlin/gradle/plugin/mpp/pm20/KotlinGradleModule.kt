/*
 * Copyright 2010-2021 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.gradle.plugin.mpp.pm20

import org.gradle.api.ExtensiblePolymorphicDomainObjectContainer
import org.gradle.api.GradleException
import org.gradle.api.NamedDomainObjectSet
import org.gradle.api.Project
import org.gradle.api.publish.maven.MavenPublication
import org.jetbrains.kotlin.gradle.utils.lowerCamelCaseName
import org.jetbrains.kotlin.project.model.*
import javax.inject.Inject

open class KotlinGradleModuleInternal(
    final override val project: Project,
    final override val moduleClassifier: String?
) : KotlinGradleModule {

    @Inject
    constructor(project: Project, moduleName: CharSequence) : this(
        project,
        moduleName.takeIf { it != KotlinGradleModule.MAIN_MODULE_NAME }?.toString()
    )

    override val moduleIdentifier: KotlinModuleIdentifier =
        LocalModuleIdentifier(project.currentBuildId().name, project.path, moduleClassifier)

    override val fragments: ExtensiblePolymorphicDomainObjectContainer<KotlinGradleFragment> =
        project.objects.polymorphicDomainObjectContainer(KotlinGradleFragment::class.java)

    // TODO DSL & build script model: find a way to create a flexible typed view on fragments?
    override val variants: NamedDomainObjectSet<KotlinGradleVariant> by lazy {
        fragments.withType(KotlinGradleVariant::class.java)
    }

    override val plugins: Set<KpmCompilerPlugin> by lazy {
        mutableSetOf<KpmCompilerPlugin>().also { set ->
            project
                .plugins
                .withType(GradleKpmCompilerPlugin::class.java)
                .mapTo(set, GradleKpmCompilerPlugin::kpmCompilerPlugin)
        }
    }

    final override var publicationMode: ModulePublicationMode = Private
        private set

    private var setPublicHandlers: MutableList<() -> Unit> = mutableListOf()

    override fun ifMadePublic(action: () -> Unit) {
        if (isPublic) action() else setPublicHandlers.add(action)
    }

    override fun makePublic(modulePublicationMode: PublishedModulePublicationMode) {
        if (publicationMode != Private) {
            if (publicationMode != modulePublicationMode)
                throw GradleException("$this is already published with mode $publicationMode, can't publish with $modulePublicationMode")
            else return
        }
        publicationMode = modulePublicationMode
        setPublicHandlers.forEach { it() }
    }

    internal val publicationHolder by lazy { DefaultSingleMavenPublishedModuleHolder(
        this,
        defaultPublishedModuleSuffixProvider = { (publicationMode as? Standalone)?.defaultArtifactIdSuffix ?: moduleClassifier }
    ) }

    override fun toString(): String = "$moduleIdentifier (Gradle)"
}

internal val KotlinGradleModule.resolvableMetadataConfigurationName: String
    get() = lowerCamelCaseName(name, "DependenciesMetadata")

internal val KotlinGradleModule.isMain
    get() = moduleIdentifier.moduleClassifier == null

internal fun KotlinGradleModule.disambiguateName(simpleName: String) =
    lowerCamelCaseName(moduleClassifier, simpleName)

internal fun KotlinGradleModule.variantsContainingFragment(fragment: KotlinModuleFragment): Iterable<KotlinGradleVariant> =
    variants.filter { fragment in it.refinesClosure }