---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
---

**consys** allows you to easily write programs with distributed, replicated data. It is [available](install.md) as an extension to *Java*.


# Features

<!--
| Distribution           | Consistency                   | Correctness |
|:------------------------|:------------------------------|:----------------------|
|   hmm        | good swedish fish | nice  |
-->

* **Distribution.** Easily distribute your your data. Use your already defined Java objects and replicate them across multiple devices.
```java
JRef<String> string1 = sys.replicate(new MyClass());
```

* **Consistency.** Boost performance or increase consistency by simply stating your desired replication strategy as a *consistency level*.
```java
JRef<@Weak String> string1 = ...
```

* **Correctness.** The special *consistency type system* ensures that consistency guarantees can not be corrupted.
```java
JRef<@Weak String> string1 = sys.replicate("Hello World!");
JRef<@Strong String> string2 = string1; //type error!
```


<!--
ust create a new *replicated object* and consys manages the rest.

, you can define the [*consistency model*](https://jepsen.io/consistency) which defines how changes of your replicated data are propageted. For example, it may suffice to not immediately propagate changes and allow concurrent updates in order to gain performance. consys lets you define your desired consistency model separately for each object as part of a consistency type.

that ensures correct mixing objects with with different consistency models. Incompatible consistency models can not be mixed in a way that would corrupt consistency guarantees, while still allowing mixing where it is sensible.
-->

# Try it out

[**consys** is available on GitHub](https://github.com/allprojects/consistency-types-impl). Follow the [installation instructions](install.md) to get started.
