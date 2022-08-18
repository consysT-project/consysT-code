package de.tuda.stg.consys.demo.twitterclone.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Date;
import java.util.UUID;

public interface ITweet extends Serializable {
    UUID getId();

    Ref<? extends IUser> getUser();

    String getBody();

    Date getCreated();

    @Transactional
    int getRetweets();

    @Transactional @StrongOp
    void retweet();
}
