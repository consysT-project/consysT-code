# Consistency Types

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
3. Run `mvn org.apache.maven.plugins:maven-dependency-plugin:properties`
4. Install the consys-maven-plugin. `cd consys-maven-plugin && mvn install`.
4. Build the complete project. Run `mvn install` in the project directory.

    
### IntelliJ

In IntelliJ, you have to add the annotation processor manually.

1. Go to `Preferences > Annotation Processors`. You can try to check `Obtain from project`. 
IntelliJ may be able to retrieve the correct checker by default. If it can, you are already finished.

2. Add the compiled jar of the consistency-checker project

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

* **consistency-checker**: Implements the type annotations and the information flow analysis using the 
Checker framework.
    * **consistency-checker-test**: Unit tests for checking information flow with the
     consistency checker. (Has its own maven module, because
    it needs to be compiled using the consistency checker as annotation processor). 
* 

## Students

This project is based on the work of Victor Schümmer and Jesper Schlegel as part of the IMPL project WS 2017-18.
