package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Date;

public class Comment implements Serializable {
    public int rating;
    @Immutable String message;
    Ref<? extends IUser> fromUser;
    Ref<? extends IUser> toUser;
    Date date;

    public Comment(int rating, String message, Ref<? extends IUser> fromUser, Ref<? extends IUser> toUser) {
        this.rating = rating;
        this.message = message;
        this.fromUser = fromUser;
        this.toUser = toUser;
        this.date = new Date();
    }
}
