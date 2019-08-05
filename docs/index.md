# What is ConSysT?

**ConSysT** is a language and middleware to write *distributed software* with datatypes that are replicated across the network.
Datatypes feturing *different consistency models* can be mixed safely because consistency is expressed in the types and the type system checks that mixing different levels cannot go wrong.

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
