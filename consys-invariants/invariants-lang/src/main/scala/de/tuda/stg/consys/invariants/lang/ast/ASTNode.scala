package de.tuda.stg.consys.invariants.lang.ast

import de.tuda.stg.consys.invariants.lang.ast.ASTNode.NodeId

trait ASTNode {
  def nodeId : NodeId
}

object ASTNode {

  type NodeId = Long

  private var currentNodeId = 0

  def freshNodeId() : NodeId = {
    currentNodeId = currentNodeId + 1
    currentNodeId
  }
}

