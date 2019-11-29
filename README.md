# Consistency Types

Find our website at https://allprojects.github.io/consistency-types-impl/.

In replicated datastores, users have to decide between available and consistent data.
Consistency ensures that the data is the same across all replicas, whereas availability
ensures that the user will get an answer from the datastore even in the presence of
network partitions. Having consistency and availability simultaneously is not possible
as described by the famous CAP theorem: available data only provides weak consistency guarantees, and
consistent data provides low availability.

However, applications often need available data to provide performance and consistency guarantees
for critical program parts, e.g., payment. When mixing available and consistent data, developers
have to reason about which consistency guarantees are still satisfied.  

This project implements consistency types that help developers mix available and consistent data;
the types are implemented as type annotations.
The checking is done using an information flow analysis.


## Installation of the project

The following instructions have been tested for *Linux Mint 19*.

 The project is built using Apache Maven.

1. Install [Maven](https://maven.apache.org)
2. Open a terminal in the main folder consistency-types-impl
3. Build the complete project. Run `mvn install` in the project directory. Use `-DskipTests` to skip tests.

To use consys in your project just add the Java API as a dependency:

    <dependency>
        <groupId>de.tuda.stg.consys</groupId>
        <artifactId>consys-japi</artifactId>
        <version>2.0.0</version>
    </dependency>
 


To enable the type checker and compiler plugin, add the following to your `pom.xml`:

    <build>
        <plugins>
            <plugin>
                <groupId>org.apache.maven.plugins</groupId>
                <artifactId>maven-compiler-plugin</artifactId>
                <configuration>
                    <compilerArguments>
                        <Xmaxerrs>10000</Xmaxerrs>
                        <Xmaxwarns>10000</Xmaxwarns>
                    </compilerArguments>
                    <annotationProcessorPaths>
                        <!-- path to the consys type checker -->
                        <path>
                            <groupId>de.tuda.stg.consys</groupId>
                            <artifactId>consys-type-checker</artifactId>
                            <version>2.0.0</version>
                        </path>
                        <!-- path to the consys javac plugin -->
                        <path>
                            <groupId>de.tuda.stg.consys</groupId>
                            <artifactId>consys-compiler</artifactId>
                            <version>2.0.0</version>
                        </path>
                    </annotationProcessorPaths>
                    <annotationProcessors>
                         <!-- Add all the checkers you want to enable here -->
                         <annotationProcessor>de.tuda.stg.consys.checker.ConsistencyChecker</annotationProcessor>
                    </annotationProcessors>
                    <compilerArgs>
                        <arg>-AprintErrorStack</arg>
                        <!-- location of the annotated JDK, which comes from a Maven dependency -->
                        <arg>-Xbootclasspath/p:${annotatedJdk}</arg>
                        <!-- Uncomment the following line to turn type-checking warnings into errors. -->
                        <!-- <arg>-Awarns</arg> -->
                        <!-- Add the consys compiler plugin for preprocessing sources -->
                        <arg>-Xplugin:ConsysPlugin</arg>
                    </compilerArgs>
                </configuration>
            </plugin>
        </plugins>
    </build>

    <dependencies>
        <dependency>
            <groupId>de.tuda.stg.consys</groupId>
            <artifactId>consys-japi</artifactId>
            <version>2.0.0</version>
        </dependency>
        <dependency>
            <groupId>de.tuda.stg.consys</groupId>
            <artifactId>consys-type-checker</artifactId>
            <version>2.0.0</version>
        </dependency>
        <dependency>
            <groupId>de.tuda.stg.consys</groupId>
            <artifactId>consys-compiler</artifactId>
            <version>2.0.0</version>
        </dependency>
    </dependencies>

The type checker enables secure information flow. The compiler plugin allows to directly use operations on `JRef`
with `ref()`.


### Cassandra

You need Cassandra 4.0+ to run with Java 11.

If using ccm then use `ccm setdir` to set the correct Cassandra install directory. 
The cassandra version is found in opt/cassandra.




### IntelliJ

In IntelliJ, you have to add the annotation processor manually.

1. Go to `Preferences > Annotation Processors`. You can try to check `Obtain from project`.
IntelliJ may be able to retrieve the correct checker by default. If it can, you are already finished.

2. Add the compiled jar of the consys-type-checker project

3. Add the checker.jar from the CheckerFramework

4. Choose `de.tu_darmstadt.consistency_types.checker.ConsistencyChecker` as annotation processor.  


## The consistency checker
The consistency checker module contains a checker for the [checker framework](https://checkerframework.org/). `ConsistencyChecker` can be configured as an annotation processor for the java compiler. With the java annotations `@High` and `@Low`, consistency levels can be assigned to variables. The checker ensures, that no low values can flow into a value assigned to a high variable. The default level for unannotated variables is `@Low`.  
Example use:  
`@High int a;`  
`int b = 42;`  
`// This assignment is not allowed and will throw assignment.type.incompatible at compile time.`  
`a = b;`  
For further examples, refer to the testcases.


## Project overview

* **consys-type-checker**: Implements the type annotations and the information flow analysis using the 
Checker framework.
    * **consys-type-checker-test**: Unit tests for checking information flow with the
     consistency checker. (Has its own maven module, because
    it needs to be compiled using the consistency checker as annotation processor). 
* 

## Students

This project is based on the work of Victor Schümmer and Jesper Schlegel as part of the IMPL project WS 2017-18.
