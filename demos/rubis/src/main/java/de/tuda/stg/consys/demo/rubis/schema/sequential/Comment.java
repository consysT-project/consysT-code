package de.tuda.stg.consys.demo.rubis.schema.sequential;

import java.util.Date;

@SuppressWarnings({"consistency"})
public class Comment {
    public int rating;
    String message;
    User fromUser;
    User toUser;
    Date date;

    public Comment(int rating, String message, User fromUser, User toUser) {
        this.rating = rating;
        this.message = message;
        this.fromUser = fromUser;
        this.toUser = toUser;
        this.date = new Date();
    }
}
