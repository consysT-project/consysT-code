# consysT

consysT is a language and middleware which allows programmers to replicate data under specified consistency levels. 
The type system ensures safe mixing of consistency levels.

The language has a binding for Java. The implementation of the middleware is in Scala.

Find more information on our website at https://consysT-project.github.io.

## How to install?

The project is built with Maven. Detailed instructions are found at https://consyst-project.github.io/install.html.

### IntelliJ

In IntelliJ, you have to add the annotation processor manually.

1. Go to `Preferences > Annotation Processors`. You can try to check `Obtain from project`.
IntelliJ may be able to retrieve the correct checker by default. If it can, you are already finished.

2. Add the compiled jar of the consys-type-checker project

3. Add the checker.jar from the CheckerFramework

4. Choose `de.tu_darmstadt.consistency_types.checker.ConsistencyChecker` as annotation processor.  



## External dependencies

These applications have to be installed and running to correctly use the system:

(For the Cassandra binding):
* Apache Cassandra 4.0.0-alpha3
* Zookeeper 3.5.6

### Cassandra

You need Cassandra 4.0+ to run with Java 11.

If using ccm then use `ccm setdir` to set the correct Cassandra install directory. 


## Project overview

* **consys-core**: Implementation of the middleware. Integrates Cassandra, Zookeeper, and/or Akka.
  
* **consys-japi**: Implementation of the frontend API for Java projects. Requires the consys-compiler Javac plugin.

* **consys-compiler**: Javac plugin for preprocessing Java API.

* **consys-type-checker**: Implementation of the type checker using the 
Checker framework.

* **integration-tests**: Fully integrated ConSysT project for testing and playing around.

* **consys-bench**: Benchmark framework.

* **demos**: Case studies and benchmarks.

* **examples**: Implementation of several libraries/case studies using ConSysT.

## Students

The main developer is Mirko Köhler under supervision of Prof. Guido Salvaneschi.

We thank the many developers that helped with the project:
* PhD students
    * Nafise Eskandani
    * Pascal Weißenburger
* Students
    * Victor Schümmer and Jesper Schlegel
    * Martin Edlund
    * Matthias Heinrich and Julian Hindelang
    * Pascal Osterwinter
    * Tobias Chen and Niklas Reiche
