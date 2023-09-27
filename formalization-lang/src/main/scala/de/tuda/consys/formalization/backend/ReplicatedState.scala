package de.tuda.consys.formalization.backend

import de.tuda.consys.formalization.lang.{Expression, FieldId}

class ReplicatedState(var fields: Map[FieldId, Expression]) extends Serializable
