**consys** is a language and middleware to write *distributed software* with datatypes that are replicated across the network.
Datatypes featuring *different consistency models* can be mixed safely because consistency is expressed in the types and the type system checks that mixing different levels cannot go wrong.

**consys** is available as an extension to Java.

# Features

* **consys** allows you to easily replicate your your own Java objects across multiple devices. Just create a new *replicated object* and **consys** manages the rest.
```java
JRef<String> string1 = sys.replicate("Hello World!");
```

* For every replicated object, you can define the [*consistency model*](https://jepsen.io/consistency) which you want to use to propagate the data. The consistency model is defined as part of a consistency type.
```java
JRef<@Weak String> string1 = sys.replicate("Hello World!");
```

* The **consys** type system checks that you are not mixing objects with incompatible consistency models. This is directly built into the language and makes writing correct programs as easy as ever!
```java
JRef<@Weak String> string1 = sys.replicate("Hello World!");
JRef<@Strong String> string2 = string1; //type error!
```

# Try it out

[**consys** is available on GitHub](https://github.com/allprojects/consistency-types-impl). Follow the [installation instructions](install.md) to get started.
