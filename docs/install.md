---
show_downloads: true 
---

If you want to use **consys** in your Java project you have to download and build the sources. As we are using the popular build tool [Apache Maven](https://maven.apache.org), the installation is simple and easy. This page explains how to install **consys** and how to use it in your project.

# How to install **consys**?

*(The following instructions have been tested with Linux Mint 19)*

You need to install the following prerequisties:

* Java 11+
* [Apache Maven](https://maven.apache.org)
* Git

Now, you can install **consys**:

1. Clone the [**consys** repository](https://github.com/allprojects/consistency-types-impl.git). The master branch contains a stable version of the project. The develop branch contains the newest features, but may be less stable.  
2. Open a terminal in the main folder `consistency-types-impl`.
3. Build the project with Maven. Run `mvn install` in the project directory. Add `-DskipTests` if you want to skip tests.
4. Done.

# How to add **consys** to your project?

*(This guide shows how to use consys in your own Maven project)*

## Minimum dependencies

After having installed **consys** locally, you can add it as a dependency to your own Maven project.

```xml
<dependency>
	<groupId>de.tuda.stg.consys</groupId>
	<artifactId>consys-japi</artifactId>
	<version>2.0.0</version>
</dependency>
```

This dependency will add the Java API to your project. Further, if you use [Aeron UDP](https://github.com/real-logic/Aeron)  as communication protocol between replicas (default), then you also need to add it as a dependency.

```xml
<dependency>
	<groupId>io.aeron</groupId>
	<artifactId>aeron-driver</artifactId>
	<version>1.22.1</version>
</dependency>
<dependency>
	<groupId>io.aeron</groupId>
	<artifactId>aeron-client</artifactId>
	<version>1.22.1</version>
</dependency>
```

## Recommended additional dependencies

These steps already suffice to use **consys** in your project. The following additions, which enable the typesystem and more convienent syntax, are recommended.


Add the **consys** type checker and the **consys** compiler plugin to your dependencies.

```xml
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
```

Further, add the following configuration for the Maven compiler plugin.

```xml
<build>
	<plugins>
		<plugin>
			<groupId>org.apache.maven.plugins</groupId>
			<artifactId>maven-compiler-plugin</artifactId>
			<configuration>
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
					<!-- enable the consys type checker -->
					<annotationProcessor>de.tuda.stg.consys.checker.ConsistencyChecker</annotationProcessor>
				</annotationProcessors>
				<compilerArgs>
					<!-- Add the consys compiler plugin for preprocessing sources -->
					<arg>-Xplugin:ConsysPlugin</arg>
				</compilerArgs>
			</configuration>
		</plugin>
	</plugins>
</build>
```

Now you are ready to enjoy **consys**!


# How to use **consys** in your code?

*(This description assumes that you followed the receommended steps from the previous section)*

When you want to use **consys** in your Java program, you have to import the Java API as well as the annotations for the type checker.

```java
import de.tuda.stg.consys.japi.*;
import de.tuda.stg.consys.checker.qual.*;
```

Now, we introduce how to test out **consys** in a local setting.

## Setting up a local replica system

If you just want to try out **consys**, the easiest wayt to do this is in a local setting. **consys** provides an easy interface for trying it out locally.

First, you create a bunch (in this case 4) of local replica systems

```java
JReplicaSystem[] systems = JReplicaSystems.fromActorSystemForTesting(4);
```

## Setting up a distributed replica system

Distributed replica systems are easiest setup using a config file. For that you can create a new config file in your resources folder `src/main/resources/consys.conf` (or anywhere else). An example configuration file is shown below.

```apacheconf
consys {
  # Define the address where this replica is hosted.
  address = "172.34.15.102:3776"

  # Define where other replicas are hosted (can include the own replica but will be ignored).
  others = [ "172.34.15.102:3776", "172.34.38.123:3776", "172.34.3.24:3776", "172.34.65.199:3776"]

  # The timeout for operations on the replica system
  timeout = 30 s
}
```

Now, you can create the replica system in your Java code by specifying the path to the configuration file.

```java
JReplicaSystem system = JReplicaSystems.fromActorSystem("consys.conf");
```


## Using a replica system

Now **consys** can be used to replicate any (serializable) Java objects. For example, assume you have the two classes below:

```java
public class ObjA implements Serializable {
	public int f = 0;

	public void inc() {
		f = f + 1;
	}
}


public class ObjB implements Serializable {
	public int g = 0;
	public JRef<@Strong ObjA> a;

	public ObjB(JRef<@Strong ObjA> a) {
		this.a = a;
	}

	public void incAll() {
		g = g + 1;
		a.ref().inc();
	}
}
```

You can create replicated objects from these classes in any replica system:

```java
JReplicaSystem sys = ... //Either the local or distributed replica system that was created above
JRef<@Strong ObjA> a = sys.replicate(new ObjA(), JConsistencyLevels.STRONG);
JRef<@Weak ObjB> b = sys.replicate("b", new ObjB(a), JConsistencyLevels.WEAK);
```

You can call methods or access fields of replicated objects using `ref()`:

```java
b.ref().incAll();
```

**consys** automatically replicates method calls or field accesses to other replica system using the specified consistency level. At the point of writing this introduction, the only supported levels are `WEAK` and `STRONG`. We are working hard to include additional levels.
