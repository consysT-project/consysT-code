package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.ClassType

object Natives {
    val topType: ClassType = ClassType(topClassId, Seq.empty, Seq.empty)
}
