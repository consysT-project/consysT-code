package de.tuda.stg.consys.demo.rubis.schema.datacentric;

import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.demo.rubis.schema.ItemStatus;

import java.io.Serializable;

public @Strong class StatusBox implements Serializable {
    public ItemStatus value;

    public StatusBox(@Mutable @Strong ItemStatus value) {
        this.value = value;
    }
}
