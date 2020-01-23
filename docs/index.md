**consys** is a language and middleware to write *distributed software* with datatypes that are replicated across the network.
Datatypes featuring *different consistency models* can be mixed safely because consistency is expressed in the types and the type system checks that mixing different levels cannot go wrong.

**consys** is available as an extension to Java.

# Features

* **Easily replicate your data.** consys allows you to easily replicate your your own Java objects across multiple devices. Just create a new *replicated object* and consys manages the rest.
```java
JRef<String> string1 = sys.replicate("Hello World!");
```

* **Define the desired replication strategy.** For every replicated object, you can define the [*consistency model*](https://jepsen.io/consistency) which defines how changes of your replicated data are propageted. For example, it may suffice to not immediately propagate changes and allow concurrent updates in order to gain performance. consys lets you define your desired consistency model separately for each object as part of a consistency type.
```java
JRef<@Weak String> string1 = ...
```

* **Strong consistency guarantees can not be corrupted.** consys a special *consistency type system* that ensures correct mixing objects with with different consistency models. Incompatible consistency models can not be mixed in a way that would corrupt consistency guarantees, while still allowing mixing where it is sensible.
```java
JRef<@Weak String> string1 = sys.replicate("Hello World!");
JRef<@Strong String> string2 = string1; //type error!
```

# Try it out

[**consys** is available on GitHub](https://github.com/allprojects/consistency-types-impl). Follow the [installation instructions](install.md) to get started.
