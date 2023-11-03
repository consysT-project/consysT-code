package de.tuda.stg.consys.invariants.lib.crdts;

public class AddOnlyDAG {
}

//FROM: https://github.com/verifx-prover/verifx/blob/main/examples/CRDT%20Verification/src/main/verifx/org/verifx/crdtproofs/graphs/AddOnlyDAGSB.vfx
///*
// * State-based implementation of an Add-only Monotonic DAG CRDT.
// * The implementation keeps two Grow-only Sets, one for the vertices and one for the edges,
// * because vertices and edges cannot be removed from the DAG.
// * The implementation corresponds to Specification 17 in the paper "A Comprehensive Study Of CRDTs".
// * The implementation of `merge` merges the underlying `GSet`s.
// */
//
//class AddOnlyDAGSB[V](vertices: GSet[V], edges: GSet[Edge[V]]) extends CvRDT[AddOnlyDAGSB[V]] {
//		def hasVertex(vertex: V) =
//		this.vertices.lookup(vertex)
//
//		def hasEdge(edge: Edge[V]) =
//		this.edges.lookup(edge)
//
//		def addEdge(from: V, to: V) = {
//		new AddOnlyDAGSB(
//		this.vertices,
//		this.edges.add(new Edge(from, to)))
//		}
//
//		// Adds a new vertex `v` between `u` and `w`
//		def addBetween(u: V, v: V, w: V) = {
//		new AddOnlyDAGSB(
//		this.vertices.add(v),
//		this.edges.add(new Edge(u, v)).add(new Edge(v, w)))
//		}
//
//		def merge(that: AddOnlyDAGSB[V]) = {
//		new AddOnlyDAGSB(
//		this.vertices.merge(that.vertices),
//		this.edges.merge(that.edges))
//		}
//
//		def compare(that: AddOnlyDAGSB[V]) = {
//		this.vertices.compare(that.vertices) &&
//		this.edges.compare(that.edges)
//		}
//		}
//
//		object AddOnlyDAGSB extends CvRDTProof1[AddOnlyDAGSB] /*{
//  proof AddOnlyDAGSB_works {
//    val leftSentinel = "|-"
//    val rightSentinel = "-|"
//
//    // Initialise the DAG with two sentinels and a single edge between them
//    val initialVertices = new GSet[String]().add(leftSentinel).add(rightSentinel)
//    val initialEdges = new GSet[Edge[String]]().add(new Edge(leftSentinel, rightSentinel))
//
//    // Create 2 fresh replicas
//    val dag1 = new AddOnlyDAGSB(initialVertices, initialEdges)
//    val dag2 = new AddOnlyDAGSB(initialVertices, initialEdges)
//
//    /*
//     * Make a sequence |- --> A --> C --> -|
//     * Then add B between A and C.
//     * Always check the preconditions before applying the operation!
//     * --> note that the Z3 compiler cannot automatically check the precondition at the beginning of each method
//     *     because it does not know what to return if the precondition fails
//     *     it cannot just throw an error as you would do in Scala/JS/...
//     */
//
//		val a = "A"
//		val b = "B"
//		val c = "C"
//		val dag11 =
//		dag1
//		.addBetween(leftSentinel, a, rightSentinel)
//		.addBetween(a, c, rightSentinel)
//
//		// Merge the DAGs
//		val dag22 = dag2.merge(dag11)
//
//		// Now add B between A and C
//		val dag222 = dag22.addBetween(a, b, c)
//		val dag111 = dag11.merge(dag222)
//
//		/*
//		 * Check that A, B, and C are in the graph.
//		 * Also check that A -> B -> C
//		 */
//		dag11.hasVertex(a) &&
//		dag11.hasVertex(c) &&
//		dag11 == dag22 &&
//		dag111.hasVertex(a) &&
//		dag111.hasVertex(b) &&
//		dag111.hasVertex(c) &&
//		dag111.hasEdge(new Edge(a, b)) &&
//		dag111.hasEdge(new Edge(b, c)) &&
//		dag111 == dag222
//		}
//		}
//		*/