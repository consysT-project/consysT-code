package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.demo.quoddy.schema.opcentric.Event;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Date;

public interface IEvent extends Serializable, IPost {
    void initSelf(Ref<? extends IEvent> self);

    void addSubscriber(Ref<? extends @Mutable IUser> user);

    @Transactional
    @StrongOp
    void postUpdate(@Weak @Mutable String text, @Strong @Mutable Date newDate);
}
