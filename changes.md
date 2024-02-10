# Changes made for the bachelor thesis by Niklas Reiche

## Type Checker Implementation

We created some new classes:

- The ```java/.../qual``` directory contains the added mixed and immutabilty type system qualifiers.
- The new meta-annotation ```QualifierForOperation``` is defined in the ```java/.../``` directory.
- The ```scala/.../``` directory has the new ```MixedInferenceVisitor```, ```ConsistencyQualifierHierarchy``` (, and ```ConsistencyTypeAnnotator```.)

Other than that changes were made in all other classes (except ```java/.../ConsistencyVisitor```).

### Utility methods

We moved some methods from the ```ConsistencyVisitorImpl``` to the ```TypeFactoryUtils``` (the methods that check if an invocation tree is a transaction, ref access, replicate, ...).

We also added many utility methods for use by the other checker classes in ```TypeFactoryUtils```:

- New accessors for qualifiers (e.g. ```mixedAnnotation```)
- Qualified name queries for consistent usage in the code base (```getQualifiedName```)
- queries for the presence of annotations on given elements for consistent usage in the code base (```hasAnnotation```, ```getExplicitConsistencyAnnotation```)
- methods to handle the new mixed qualifier, e.g. extracting the default op level of a given qualifer, finding an operation level on a method, ...
- methods to query the consistency qualifier for a given operation level (the mappig is also constructed and cached in this class)
- some new methods for easier finding out if a type has a given name, if members are accessible, or if methods are side-efect free for consistent usage in other classes

### Subtyping for Mixed Qualifiers

Apart from adding the mixed qualifier in the ```qual``` directory and changing the meta-annotations on the other consistency qualifiers, we add subtyping rules for the mixed qualifiers in the ```ConsistencyQualifierHierarchy``` with one method each for comparing two qualifiers w.r.t. subtyping, least upper bounds, and greatest lower bounds.

### Immutabilty subtyping

The immutabilty qualifiers are also added in the ```qual``` directory, and use the meta-annotations for defining the type hierarchy (consistency and immutabilty type system form separate hierarchies). The subtyping checks for complete types are done in the ```ConsistencyTypeHierarchy```. We added new methods to check subtyping for only the consistency part (e.g. for primitives)(```isConsystencySubtype```) and to check subtyping with the immutabilty types (```isCombinedSubtype```). The ```isSubtype``` method now chooses between the two subtype checks based on the Java type of the sub- and supertype.

### Mixed Inference Visitor

The ```MixedInferenceVisitor``` is new and is responsible for inferring the consistency qualifiers in mixed classes based on the operation levels. The simplified functionality of this class is described in the thesis.

### Consistency Visitor

The typing rules in the ```ConsistencyVisitorImpl``` were extended. New fields were needed for the new workflow described in the thesis (```classVisitCache, classVisitQueue, classVisitQueueReported```).  We added the ```processClassTree``` case to initialize the type factory, run the inference visitor and handle the iterative type checking for multiple consistency levels.

New methods were added to interface with the type factory and type annotator classes (```queueClassVisit```).

The ```checkAssignment``` method now also checks immutabilty constraints.

The ```visitMemberSelect``` case is new and checks that private members are not accessed through ```Refs```.

The ```visitMethodInvocation``` case now also checks implicit flow constraints for operation levels and immutability constraints on receviers. We also added these checks for invocations with an implicit ```this``` receiver. We added a relaxation for implicit flow constraints in method arguments if the parameter is decalred Immutable.

The ```visitMethod``` case now also checks operation level override rules and Immutabilty of return types for replicated objects.

We also added some more utility methods at the botom of the class.

In the ```InformationFlowTypeVisitor``` we added a new method to help with checking mixed method invocations w.r.t. implicit contexts (```allowAsMixedInvocation```).

We also generally changed a lot of ```getAnnotation``` calls to ```getEffectiveAnnotation``` so that wildcard bounds are included.

### Type Factory

The ```ConsistencyAnnotatedTypeFactory``` now has extra fields to track which classes are being checked at a given moment (```visitClassContext```, ```methodReceiverContext```) along with some utitility methods at the bottom of the class to query/update the fields.

We now override the ```getAnnotatedType``` and ```addComputedTypeAnnotations``` methods to disable caching when certain elements are being queried. This is needed since we implicitly reuse the Checkerframework's cache with the new workflow of checking multiple consistencies for a class. Theses overrides are primarily needed because of the new defaulting rule for mixed getters.

The ```ConsistencyTypeAnnotator``` now has a case for ```visitDeclaredType``` where we capture uses of a class in a Ref object with a specific consistency, so that we can add them to the visitor queue. The ```visitExecutable``` case is also new. Here we adapt the return types for mixed getter methods.

The ```ConsistencyTreeAnnotator``` was restructed a bit (```visitMemberSelect```) and new cases added (```visitField, visitIdentifier, visitVariable, visitMethodInvocation```) to have a cleaner adaptation of the results of field accessor and method invocation expressions. Here, the inference results for mixed classes come into play, too, since the results are queried when the qualifier of a mixed field is needed (```visitField```). We also adapted the existing TreeAnnotator cases to include Immutabilty qualifers.

### Checker Class

We added some functionality to the ```ConsistencyChecker``` (all methods), to support caching of reported errors for later (re-)throwing in the ```ConsistencyVisitorImpl```.

## Type Checker Tests

The test cases can be found in the ```./consys-type-checker/consys-type-checker-test``` subproject.

The ```src/test/java/.../OperationTest``` runs all tests under the ```tests/testfiles/operations``` directory, which are the new test cases for the features implemented in this thesis.

The ```src/test/java/.../CaseStudyTest``` runs all tests under the ```tests/per-directory/thesis-case-studies``` directory, which contains the code for the case studies in the ConSysT-Op version used for the evaluation.

## Evaluation Code

The code used for the evaluation is in the ```./thesis-test``` subproject.

The two ```*_results.txt``` files contain the results of the benchmarks used in the evaluation chapter.

The source directory contains a ```Main``` class, which has the code for running the compilation time benchmark.

The ```bench``` module contains code for running the runtime benchmark. The ```Demo``` class is the entry point.

The ```demos``` module contains the case study implementations sorted by case study and language version.

Executing the benchmark for the old type checker version requires changing dependencies in the ```pom.xml``` file and compiling the old type checker project under a different type checker name. The coresponding measurement runs are therefore commented out in the ```Main``` class.
