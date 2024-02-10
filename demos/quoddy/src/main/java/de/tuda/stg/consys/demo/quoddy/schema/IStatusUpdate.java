package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Weak;

import java.io.Serializable;
import java.util.List;

public interface IStatusUpdate extends Serializable, IPost {
    void setText(@Weak @Mutable String text);

    String getText();

    @Override
    @Transactional
    String toString();
}
