package de.tuda.stg.consys.invariants.lib.crdts;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.invariants.lib.crdts.data.*;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.replicaId;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.stateful;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.object;

@ReplicatedModel
public class TwoPTwoPGraph implements Mergeable<TwoPTwoPGraph> {

	public final TwoPhaseObjectSet vertices = new TwoPhaseObjectSet();
	public final TwoPhaseEdgeSet edges = new TwoPhaseEdgeSet();


	//@ public invariant (\forall Edge edge; edges.contains(edge); vertices.contains(edge.from) && vertices.contains(edge.to));

	//@ ensures vertices.isEmpty();
	//@ ensures edges.isEmpty();
	public TwoPTwoPGraph() {

	}

	//@ assignable \nothing;
	//@ ensures \result == vertices.contains(v);
	public boolean hasVertex(Object v) {
		return vertices.contains(v);
	}

	//@ assignable vertices;
	//@ ensures stateful( vertices.add(v) );
	public Void addVertex(Object v) {
		vertices.add(v);
		return null;
	}

	//TODO: Just the stateful call is not enough "stateful( edges.add( object(Edge.class, from, to) ) );" because it does not talk about the other elements of the set.
	//@ requires vertices.contains(from) && vertices.contains(to);
	//@ assignable edges;
	//@ ensures (\forall Edge edge; edges.contains(edge); \old(edges).contains(edge) || edge == object(Edge.class, from, to));
	public Void addEdge(Object from, Object to) {
		if (!vertices.contains(from) && !vertices.contains(to))
			throw new IllegalArgumentException();

		edges.add(new Edge(from, to));
		return null;
	}


	//@ requires (\forall Edge edge; edges.contains(edge); edge.from != v && edge.to != v);
	//@ assignable vertices;
	//@ ensures stateful( vertices.remove(v) );
	public Void removeVertex(Object v) {
		for (Edge edge : edges.getValue()) {
			if (edge.to.equals(v) || edge.from.equals(v))
				throw new IllegalArgumentException();
		}

		vertices.remove(v);
		return null;
	}


	//@ assignable edges;
	//@ ensures (\forall Edge edge; edges.contains(edge); \old(edges).contains(edge) && edge != object(Edge.class, from, to));
	public Void removeEdge(Object from, Object to) {
		edges.remove(new Edge(from, to));
		return null;
	}


	//@ ensures stateful( vertices.merge(other.vertices) );
	//@ ensures stateful( edges.merge(other.edges) );
	public Void merge(TwoPTwoPGraph other) {
		vertices.merge(other.vertices);
		edges.merge(other.edges);

		return null;
	}
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