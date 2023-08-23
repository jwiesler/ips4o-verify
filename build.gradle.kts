import io.github.gradlenexus.publishplugin.NexusRepositoryContainer
import java.time.Duration

plugins {
    `java-library`
    signing
    `maven-publish`
    id("io.github.gradle-nexus.publish-plugin") version "1.0.0"
    idea
    id("com.diffplug.spotless") version "6.20.0"
}

group = "org.key-project.ips4o"
version = "1.0"

// configure all java components to be published
publishing {
    publications {
        create<MavenPublication>("maven") {
            from(components.getByName("java"))
            pom {
                //name = "${project.group}:${project.name}"
                description = "A fast and formally verified sorting algorithm."
                url = "https://github.com/keyproject/ips4o-verify"
                licenses {
                    license {
                        name = "Simplified BSD License"
                        url = "https://opensource.org/licenses/BSD-2-Clause"
                    }
                }
                developers {
                    developer {
                        id = "jwiesler"
                        name = "Julian Wiesler"
                        email = "wiesleju@gmail.com"
                        roles = setOf("developer", "verifier")
                    }

                    developer {
                        id = "witt"
                        name = "Sascha Witt"
                        email = "sascha.witt@kit.edu"
                        roles = setOf("developer")
                    }

                    developer {
                        id = "mattulbrich"
                        name = "Mattias Ulbrich"
                        email = "ulbrich@kit.edu"
                        roles = setOf("verifier")
                        url = "https://formal.iti.kit.edu/ulbrich"
                        organization = "Karlsruhe Institute of Technology"
                        organizationUrl = "https://formal.iti.kit.edu"
                    }
                }

                contributors {
                    contributor {
                        name = "Alexander Weigl"
                        email = "weigl@kit.edu"
                        roles = setOf("maintainer")
                        url = "https://formal.iti.kit.edu/weigl"
                        organization = "Karlsruhe Institute of Technology"
                        organizationUrl = "https://formal.iti.kit.edu"
                    }
                }

                issueManagement {
                    system = "Github"
                    url = "https://github.com/keyproject/ips4o-verify/issues"
                }


                scm {
                    connection = "scm:git:https://github.com/keyproject/ips4o-verify"
                    developerConnection = "scm:git:ssh://github.com/keyproject/ips4o-verify.git"
                    url = "https://github.com/keyproject/ips4o-verify"
                }
            }
        }
    }
}


// ossrh requires javadoc and sources https://central.sonatype.org/pages/requirements.html
java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8

    withJavadocJar()
    withSourcesJar()
}

signing {
    sign(publishing.publications["maven"])
}

nexusPublishing {
    repositories(Action<NexusRepositoryContainer> {
        sonatype {
            nexusUrl.set(uri("https://s01.oss.sonatype.org/service/local/"))
            snapshotRepositoryUrl.set(uri("https://s01.oss.sonatype.org/content/repositories/snapshots/"))
        }
    })

    // these are not strictly required. The default timeouts are set to 1 minute. But Sonatype can be really slow.
    // If you get the error "java.net.SocketTimeoutException: timeout", these lines will help.
    connectTimeout = Duration.ofMinutes(3)
    clientTimeout = Duration.ofMinutes(3)
}

// verification

val keyClasspath: Configuration = configurations.create("key")
val keyClasspathOverflow: Configuration = configurations.create("keyoverflow")
dependencies {
    keyClasspath(files("tools/key-2.11.0-exe.jar", "tools/citool-1.4.0-mini.jar"))
    keyClasspathOverflow(files("tools/key-2.11.0-exe.jar", "tools/citool-1.4.0-mini.jar"))
}

val mainClassName = "de.uka.ilkd.key.CheckerKt"

fun JavaExec.checkCommand() {
    mainClass = "de.uka.ilkd.key.CheckerKt"
    classpath = keyClasspath
    systemProperty("key.contractOrder", "contract-order.txt")
    args("--no-auto-mode", "--proof-path", "proofs/", "src/main/key/project.key")
    group = "key"
    tasks.named("check").get().dependsOn(this)
}

fun JavaExec.checkOverflowCommand() {
    mainClass = "de.uka.ilkd.key.CheckerKt"
    systemProperty("key.contractOrder", "contract-order.txt")
    args("-v", "--no-auto-mode", "--proof-path", "proofs-overflow/", "src/main/key/project.key")
    classpath = keyClasspathOverflow
    group = "key"
    tasks.named("check").get().dependsOn(this)
}

tasks.create<JavaExec>("run") {
    mainClass = "de.uka.ilkd.key.core.Main"
    classpath = files("tools/key-2.11.0-exe.jar", "tools/citool-1.4.0-mini.jar")
    systemProperty("key.contractOrder", "contract-order.txt")
}

tasks.create<JavaExec>("checkAll") {
    checkCommand()
    args("--forbid-contracts", "-file", "contracts/ignore.txt", "-s", "statistics.json")
}

tasks.create<JavaExec>("checkMethods") {
    checkCommand()
    args(
        "--forbid-contracts", "-file", "contracts/ignore.txt", "-s", "statistics-methods.json",
        "--forbid-contracts-file", "contracts/constructors.txt"
    )
}

tasks.create<JavaExec>("checkConstructors") {
    checkCommand()
    args("--contracts-file", "contracts/constructors.txt", "-s", "statistics-constructors.json")
}

tasks.create<JavaExec>("checkClassTarget")
{
    checkCommand()
    args(
        "--forbid-contracts",
        "-file",
        "contracts/ignore.txt",
        "--contracts-filter",
        """^de.wiesler.{{target}}[.*""",
        "-s",
        "statistics.json"
    )
}

tasks.create<JavaExec>("checkOverflowMethods") {
    checkOverflowCommand()
    args(
        "--contracts-file", "contracts/overflow.txt", "--forbid-contracts-file", "contracts/constructors.txt",
        "-s", "statistics-overflow-methods.json"
    )
}

tasks.create<JavaExec>("checkOverflowConstructors") {
    checkOverflowCommand()
    args("--contracts-file", "contracts/constructors.txt", "-s", "statistics-overflow-constructors.json")
}
