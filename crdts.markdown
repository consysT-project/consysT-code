# Notes

We are working with state-based CRDTs: synchronization is easier and they are by default causal consistent.

<!--
 D1, D2 are CRDTs that support operations p and q, respectively. We write D1, D2 when the supported operations are clear.
-->

Operations are always executed (a) atomically: they are the smallest change that a system can observe, and (b) in local isolation: changes from other processes are not visible during the execution of an operation.

P_1 is a process that owns D1_1 and D2_1. P_2 respectively. When P_1 is executing an operation, then it is executed on its owned replica, i.e. P_1:{ D1 <- p(v) } = P_1:{D1_1 <- p(v)}. A process can not execute operations on replicas owned by other processes. Every process has a replica of each CRDT (*this is a simplifying assumption. Let's see if we need it!*).
We assume that processes are logically single-threaded.



We distinguish between CRDTs (D1, D2) and CRDT replicas (D1_1, D1_2). Programmers are not exposed to replicas, but can only view the CRDT as a whole.


* Example:
	A program on process P_1 is written as:
	```
	P_1:{
		x <- p(v1)
		y <- q(v3)		
		x <- p(v2)
	}
	```
	`x` and `y` point to CRDTs. `p`, `q` are operation ids, p(v), q(v) are (basic) operations with id p, q, respectively, and argument v.
	This program does not have any isolation guarantees (a) across CRDTs or (b) on a single CRDT. `p(v2)` can be executed on a state of D1 that comes from another process. Note that the operation `p(v1)` is reflected in that state however.

## Language

We are providing a simple language to specify the exact semantics of our system.

First we formalize CRDT (replicas) and operations.
`op : Op` is an operation (which we will define in the grammar below). `bop: BOp` are basic operations. For now, all operations are basic operations. We will extend this later. The definition of an operation `[[.]] : BOp -> State -> Val x State` takes the state of an CRDT and produces a return value and a changed state.
`D = (S, I, [[.]], lub)` is a CRDT specification, where `S` is the current state of the CRDT, `I` is the initial state, `[[.]]` are the operation definitions of this CRDT, and `lub: State -> State -> State` is a least upper bound on states. In particular, states `S` are ordered in a semilattice, where `lub` is the least upper bound (and `<` is the inferred smaller-eq operator). The state `S` can for example be a set or a map.
We write `[[.]]_D` for the operations of `D`.

* Syntax
	`v: Val` are values.
	`p`,`q` are operation names.
	`x: Var` are variables.
	```
	(Process) P_n ::= { e }
	(Basic Operation) bop ::= p(v)
	(Operation) op ::= bop
	(Expression) e ::= e ; e  |  x <- op | skip
	```

We now give the semantics. We start with defining the state of CRDT replicas.

Every process stores its local replicas in a store `SS: Var -> D` that maps variables to the local state at the replica. We assume that the same variables on different processes map to the same CRDT (although to different local replicas of course).
We assume that every variable has already been initialized and that the variables on all processes map to the same "type" of CRDT. Intuitively, to CRDTs have the same type if they have the same initial state, operations, and lub. The local state can be different.

* Dynamic semantics
	We start with defining local transitions, i.e. how operations effect the state of a local replica. The configuration of a local replica `K = (SS, e)` is defined as the local states of all replicas and the expression that is next to be evaluated.
	For the dynamic semantics of expressions, we are using the judgment `n |- K ~> K'` evaluating a configuration to another configuration.

	Semantics for expressions:
	```
	SS(x) = (S, I, [[.]], lub)
	SS' = SS, x -> [[p(v)]](S)
	-----------------------------------
	n |- (SS, x <- p(v)) ~> (SS', skip)

	n |- (SS, e1) ~> (SS', e1')
	-------------------------------------
	n |- (SS, e1 ; e2) ~> (SS', e1' ; e2)

	--------------------------------
	n |- (SS, skip ; e2) ~> (SS, e2)
	```

	The whole system consists of multiple processes running in parallel. The global transitions use the judgment `|- (K_1, ..., K_n) ~~> (K_1', ..., K_n')` where `K_1` is the configuration for process `P_1`.
	`merge` is a function that merges two CRDT states and gives a new state. In particular, `merge` is associative, commutative, and idempotent.

	Semantics for programs:
	```
	i |- K_i ~> K_i'
	---------------------------------------
	|- (..., K_i, ...) ~~> (..., K_i', ...)

	K_i = (SS_i, e_i)	K_j = (SS_j, e_j)
	SS_i(x) = (S_i, I_i, [[.]]_i, lub_i)
	SS_j(x) = (S_j, I_j, [[.]]_j, lub_j)
	SS_j' = SS_j, x -> (lub_j(S_i, S_j), I_j, [[.]]_j, lub_j)
	-----------------------------------------------------------
	|- (..., K_i, ..., K_j, ...) ~~> (..., K_i, ..., K_j', ...)

	Note: As SS_i(x) and SS_j(x) have to be the same "type" of CRDT, I_i = I_j, [[.]]_i = [[.]]_j, and lub_i = lub_j.
	```


## Adding weak, atomic transactions

We are slowly adding transactions for multi-object isolation. What we want to achieve is something like this:

```
P_1:{
	tx {
		x <- p(v1)
		y <- q(v3)
	}
	x <- p(v2)
}
```

In this example, `p(v1)` and `q(v3)` are executed inside of a transaction. That means that (a) there are no changes from other processes visible between the operations (the whole transactions runs on the local state before synchronizing), and (b) when another process observes one of the operations, it observes all of them.
We call a transaction that satisfies these constraints a *weak transaction*.

* Definition: *weak transaction*
	A weak transaction is a sequence of operations that satisfy the following two constraints:
	* *Local isolation*: Changes from other processes are not visible on the process until the weak transaction has committed.
	* *Atomicity*: Processes either see all operations of the transaction or none.

Using this definition, we can say that a weak transaction is an operation *on multiple objects (CRDTs)* that consists of other operations.
We are exploring how weak transactions can be sensibly implemented with CRDTs.


## Batch operations

Batch operations are operations that are composed of a sequence of other operations. We write `D1 <- {p(v1), p(v2)}` for a batch operation consisting of operation `p(v1)` and `p(v2)`.

Batch operations are a simple addition to CRDTs. Executing a batch operation entails executing all the sub-operations. As operations are executed with atomicity and local isolation by default, batch operations provide the same guarantees.

Let's extend the syntax with batch operations:
```
(Operation) op ::= ... | {op, op}
```
You can use nested batch operations to define larger batches for operations.

As batch operations are no basic operations, we have to give the semantics for batch operations `[[.]]^BATCH_D` on a CRDT `D`:
```
[[p(v)]]^BATCH_D = [[p(v)]]_D
[[{op1, op2}]]^BATCH_D = [[op1]]_D ° [[op2]]_D` (function composition)
```

We can then change the existing operation rule in the dynamic semantics.
```
SS(x) = (S, I, [[.]], lub) =: D
SS' = SS, x -> [[op]]^BATCH_D(S)
-----------------------------------
n |- (SS, x <- op) ~> (SS', skip)
```

We do not have to change the global semantics. The local semantics guarantee atomicity and local isolation.


## Coordinating operations

When we want to extend the definition of operations to be executed atomically for multiple objects we have to coordinate operations between CRDTs.

Let's first define combinations of CRDTs into a single CRDT. We will use the cross product of CRDTs:
```
D1 = (S1, I1, [[.]]_D1, lub_1)
D2 = (S2, I2, [[.]]_D2, lub_2)

D1 X D2 = (
	S := S1 x S2,
	I := I1 x I2,
	[[.]] : BOp + BOp -> S -> Val x S =
		case (Left(bop), (s1, s2)) -> (v1', (s1', s2))
			where (v1', s1') := [[bop]]_D1(s1)
		case (Right(bop), (s1, s2)) -> (v2', (s1, s2'))
			where (v2', s2') := [[bop]]_D2(s2),
	lub (s1,s2) (s1',s2') = (lub_1 s1 s1', lub_2 s2 s2')
)
```

We can use this construction and batch operations to get operations that are atomic on multiple objects:
```
x X y <- { Left(p(v1)), Right(q(v3)) }
```

There is one problem though: the amount of concurrency is drastically reduced.
We need to keep in mind, that when we want to have atomicity and local isolation then all CRDTs in the program have to combine to one big CRDT with the composition above. Imagine you have a larger program with CRDTs `x1 ... xn` then when using this construction all operations are run in serial. While this is not a problem for the process itself (it runs single-threaded), it can be a problem for the synchronization algorithm, as synchronizing will block the whole system. Also, every synchronization would need to synchronize the state of all(!) CRDTs.

Question: Can this be solved with delta-crdts? Delta state-based CRDTs may be able to solve the problem with synchronizing all state.

One problem then still remains: while executing an operation all CRDTs are locked. This means that an asynchronous synchronization is not possible. **Maybe we should evaluate this to see how big the problem really is.**
