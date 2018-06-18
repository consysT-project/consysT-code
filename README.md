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


## Project overview

The project is divided into the following modules:

* **consistency-checker**: Implements the type annotations and the information flow analysis using the 
Checker framework.
    * **consistency-checker-test**: Unit tests for the consistency checker. (Has its own maven module, because
    it needs to be compiled using the consistency checker as annotation processor). 
* **consistency-store**: Implements distributed data store bindings (e.g. for Cassandra) 
for types with consistency annotations.
* **store-integration-demo**: Examples how the type annotations are used in combination with
a replicated datastore. 


## Installation of the project

The project is built using Apache Maven. 

1. Install [Maven](https://maven.apache.org)
2. Open a terminal in the main folder consistency-types-impl
3. Run `mvn org.apache.maven.plugins:maven-dependency-plugin:properties`
4. Run `mvn install`


### Cassandra

Cassandra has to run to execute the Cassandra integration.

If Cassandra should be run on only a single machine, then it is advisable to use 
CCM (Cassandra Cluster Manager, https://github.com/riptano/ccm).
This is because we need to start multiple replicas in order to use consistency
features of Cassandra.

1. Clone the Github repo and install the project (as written on the website):

    `sudo ./setup.py install`

2. Create and start a local cluster. One node has to be placed on 127.0.0.1 (this is the default behaviour).
The Cassandra version is specified by `-v` (unavailable versions are downloaded and installed automatically),
,the number of replicas is specified by `-n`, and `-s` starts the cluster.
    
    `ccm create test -v 3.11.2 -n 3 -s`
    
3. Check whether the cluster is created:

    `ccm node1 ring`
    
4. When the cluster is stopped (e.g. after a restart), then it can be started again with

    `ccm start test`

Cassandra can be started or stopped by using
    `sudo service cassandra start/stop` 
    
### IntelliJ

In IntelliJ, you have to add the annotation processor manually.

1. Go to `Preferences > Annotation Processors`. You can try to check `Obtain from project`. 
IntelliJ may be able to retrieve the correct checker by default.

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

## The cassandra connector
The Cassandra module contains a connector to the [Cassandra distributed database system](https://cassandra.apache.org/). It provides wrappers for java objects whose values are stored in cassandra. The wrappers ensure consistency on different levels between the java objects and the data in the database.  
`HighValue` objects are read from and written to ALL cassandra nodes, and each read and write access to the object is synchronized with the database. `LowValue` objects on the other hand are only written to a single cassandra node (although cassandras eventual consistency guarantees that the value will propagade over time, if no other value is written), and read accesses may be cached in the wrapper, so the read value may not be the latest written value. The only API methods of the wrappers are `value()` to read the current value and `setValue(value)` to set a new value, as well as a `perform(function)` method that executes a function with the wrappers current value as an argument. Everything else will be handled behind the scenes. To make this work, one has to provide a `java.util.function.Supplier` and a `java.util.function.Consumer` lambda function to the constructor that tells the wrapper how to read from and write to Cassandra respectively.  
Classes that have fields wrapped in `HighValue` or `LowValue` should extend the `ConsistencyObject` class, which allows reading and writing of all members at once, while the `ConsistencyObject` objects are not stored in Cassandra themselves. Additionaly there is a `CollectionWrapper` class that allows batch processing of collections of `ConsistencyObject` objects.  
It is possible to have cyclic dependencies, i.e. a `ConsistencyObject` that has another `ConsistencyObject` inside a wrapper. It is ensured, that reading and writing is only performed once so that no infinite loop occures. For an example refer to the `CycleTest` class.  
The wrappers are compatible with the consistency annotations. For example, the value of a `HighValue` will always be annotated with `@High` and no `@Low` value can be assigned to a `HighValue` wrapper. A simple example application with a bank and customers is included.

## Info

This project is based on the work of Victor Schümmer and Jesper Schlegel as part of the IMPL project WS 2017-18.
