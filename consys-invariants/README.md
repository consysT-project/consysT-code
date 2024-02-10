# ConLoc: Pre- and Postcondition Analysis for ConSysT

Consistent Local-First Software (ConLoc) is a compiler to automatically enforce safety and maintain invariants in local-first applications. 
ConLoc effectively addresses the issue of preserving invariants in the execution of replicated data types, including CRDTs. 

## Code Overview 
* `invariants-solver` contains the complete compiler with the verification procedure.
  * The compiler is started from the class `de.tuda.stg.consys.invariants.solver.Main`. 
* `invariants-examples` contains case studies.
* `invariants-lib` contains additional constructs for ConLoc's specification language.
* `invariants-lang` contains an experimental implementation for the ConLoc compiler.
