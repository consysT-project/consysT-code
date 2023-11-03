package de.tuda.stg.consys.invariants.lib.crdts;

public class TwoPTwoPGraph {
}


//FROM: https://github.com/verifx-prover/verifx/blob/main/examples/CRDT%20Verification/src/main/verifx/org/verifx/crdtproofs/graphs/TwoPTwoPGraphSB.vfx
///*
// * State-based implementation of a 2P2P-Graph CRDT.
// * Keeps a 2P-Set of vertices and a 2P-Set of edges.
// * Since it uses 2P-Sets removed vertices/edges cannot be added again.
// * An edge is considered in the graph if its vertices are in the graph and the edge between them is in the graph.
// * As a result, if a vertex V1 is removed while concurrently an edge V1 -> V2 is added,
// * the remove operation will win and the edge V1 -> V2 will no longer be in the graph since V1 is no longer in the graph.
// */
//
//class TwoPTwoPGraphSB[V](vertices: TwoPSetSB[V] = new TwoPSetSB[V](),
//		edges:    TwoPSetSB[Edge[V]] = new TwoPSetSB[Edge[V]]()) extends CvRDT[TwoPTwoPGraphSB[V]] {
//
//		override def reachable() = {
//		// A graph is valid iff E ⊆ V × V
//		// i.e. there can only be edges between existing vertices
//		this.edges.forall((edge: Edge[V]) => {
//		if (this.hasEdge(edge))
//		this.hasVertex(edge.from) && this.hasVertex(edge.to)
//		else
//		true
//		})
//		}
//
//		def hasVertex(vertex: V) =
//		this.vertices.lookup(vertex)
//
//		def hasEdge(edge: Edge[V]) = {
//		this.vertices.lookup(edge.from) &&
//		this.vertices.lookup(edge.to) &&
//		this.edges.lookup(edge)
//		}
//
//		def addVertex(vertex: V) =
//		new TwoPTwoPGraphSB(this.vertices.add(vertex), this.edges)
//
//		def addEdge(from: V, to: V) =
//		new TwoPTwoPGraphSB(this.vertices, this.edges.add(new Edge(from, to)))
//
//		def removeVertex(vertex: V) =
//		new TwoPTwoPGraphSB(this.vertices.remove(vertex), this.edges)
//
//		def removeEdge(edge: Edge[V]) =
//		new TwoPTwoPGraphSB(this.vertices, this.edges.remove(edge))
//
//		def merge(that: TwoPTwoPGraphSB[V]) = {
//		new TwoPTwoPGraphSB(
//		this.vertices.merge(that.vertices),
//		this.edges.merge(that.edges)
//		)
//		}
//
//		def compare(that: TwoPTwoPGraphSB[V]) = {
//		this.vertices.compare(that.vertices) &&
//		this.edges.compare(that.edges)
//		}
//		}
//
//		object TwoPTwoPGraphSB extends CvRDTProof1[TwoPTwoPGraphSB]