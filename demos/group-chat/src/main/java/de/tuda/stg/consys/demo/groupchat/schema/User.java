package de.tuda.stg.consys.demo.groupchat.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.List;


/**
 * message delivery (Figure 4), user creation, inbox checking, and group joining
 *
 * @author Mirko Köhler
 */
public class User implements Serializable {
    public @Mutable @ThisConsistent String name;

    public User(@Mutable @ThisConsistent String name) {
        this.name = name;
    }

    @Transactional
    public void copyName(@Mutable @ThisConsistent String name) {
        this.name = name;
    }
}
