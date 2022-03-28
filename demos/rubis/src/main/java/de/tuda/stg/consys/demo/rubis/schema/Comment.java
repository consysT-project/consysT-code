package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Date;

public class Comment implements Serializable {
    int rating;
    @Immutable String message;
    Ref<User> fromUser;
    Ref<User> toUser;
    Date date;

    public Comment(int rating, String message, Ref<User> fromUser, Ref<User> toUser) {
        this.rating = rating;
        this.message = message;
        this.fromUser = fromUser;
        this.toUser = toUser;
        this.date = new Date();
    }
}
