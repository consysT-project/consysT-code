# What is ConSysT?

**ConSysT** is a language and middleware that enables you to write *distributed code* that allows you to mix data that is replicated across the network using *different consistency models*.

**ConSysT** is available as a tool and library for Java.

# Why use ConSysT?

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

