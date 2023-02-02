# ConLoc Artifact

This artifact contains:
* The ConLoc compiler (in `conloc-invariants/conloc-compiler`): The compiler includes the translation of annotations
to constraints, as well as the verification with the z3 solver. The benchmark code for the compiler is also included here.
* The case studies (in `conloc-invariants/invariants-examples`): This folder contains the case studies from the paper.

## Installation

The artifact requires a Java installation (tested with Java 11). 

### Z3

Additionally, you need two native libraries for the Z3 solver that is used by the compiler.
These libraries are included in the artifact and ConLoc makes an effort to include the libraries automatically,
but depending on your system you **maybe** need to manually add the libraries
to the `lib` folder of your system, e.g., `/usr/lib/`.

At this point, you can try to run the artifact and only install the libraries in case of problems.

These two libraries are: 

* libz3.so (Linux) / libz3.dylib (Mac)
* libz3java.so (Linux) / libz3.dylib (Mac)

The libraries (1) can be found in the folder `conloc-invariants/conloc-compiler/lib` (built for 64-bit Linux), or 
(2) are manually generated when installing [z3](https://github.com/Z3Prover/z3) with the `--java` option.

### Maven

The artifact contains pre-built executables already. If you do not want to compile the artifact yourself, you 
can skip this section. The project is built with [Apache Maven](https://maven.apache.org/). To compile the code, 
you need to install Maven and execute `mvn install` in the project folder.


## Execution

To execute the artifact, you need the following prerequisites:

* Java 11 (newer may also work)
* Installed the Z3 libraries

The artifact is started by the `conloc` script in the project folder. 
The functionalities of the artifact are explained in the following.


### Running the compiler on a case study

You can run the compiler/checker for one of the case studies from the paper (Section 5.1). 
Case studies are identified by the name from the paper, and are started by supplying the name to the script.

```$ conloc [case-study-name]```

Possible names are: 
`consensus, joint_bank_account, distributed_lock, resettable_counter, gcounter, twophaseset, pncounter, credit_account, gset, bank_account_lww, tournament, bank_account

The output lists for every class in the case study the verification result for each of the properties from Section 3.3
in the paper. If the property is satisfied, then the tool shows VALID, otherwise it shows INVALID.

For example, executing `conloc credit-account` gives the following output for the ReplicatedCreditAccount class:

```
Result for ReplicatedCreditAccount
 | (i0) invariant/initial : VALID
 | (i1) invariant/method <getValue> : VALID
 | (i1) invariant/method <deposit> : VALID
 | (i1) invariant/method <withdraw> : VALID
 | (i2) invariant/merge : VALID
 | (m0) mergability/initial : VALID
 | (m2) mergability/weak/method <getValue> : VALID
 | (m3) mergability/strong/method <getValue> : VALID
 | (m2) mergability/weak/method <deposit> : VALID
 | (m3) mergability/strong/method <deposit> : VALID
 | (m2) mergability/weak/method <withdraw> : INVALID
 | (m3) mergability/strong/method <withdraw> : VALID
 | (m1) mergability/merge : VALID
```

Properties i0, i2, m0, and m1 appear once per class, and properties i1, m2, and m3 appear once per method.
In the example, we can see that all properties are satisfied with exception of m2 for withdraw 
(see line `(m2) mergability/weak/method <withdraw> : INVALID`).


### Running the compiler benchmarks

With the artifact you can also run the compiler benchmarks from the paper (Section 5.3). 
The compiler benchmarks for ConLoc are executed with:

`$ conloc --bench-sys`

and the compiler benchmarks for the Java compiler are executed with:

`$ conloc --bench-java`

Both benchmarks measure the execution time of the compiler on all of the case studies. 
The measurement results are shown after all case studies have been measured. 
