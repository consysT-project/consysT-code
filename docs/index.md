# What is ConSysT?

**ConSysT** is a language and middleware to write *distributed software*. 

In ConSysT, one can define datatypes replicated across the network with *different consistency models*.

Consistency levels are expressed in the type system. 

The type system checks that mixing different levels in the same application cannot go wrong.

**ConSysT** is available as a Java extension based on the Checker framework.

# Why ConSysT?

* Distribute your data across multiple devices.
```java
Ref<String> string1 = replicate("Hello World!");
```

* Define the propagation of updates to other devices as availability annotations.
```java
Ref<@High String> string1 = replicate("Hello World!");
```

* Safe mixing of different availability levels built into the type system.
```java
Ref<@High String> string1 = replicate("Hello World!");
Ref<@Low String> string2 = string1; //type error!
```
