package de.tuda.stg.consys.demo.twitterclone.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Date;
import java.util.List;
import java.util.UUID;

public interface IUser extends Serializable {
    UUID getId();

    String getUsername();

    String getName();

    Date getCreated();

    List<Ref<? extends IUser>> getFollowers();

    List<Ref<? extends IUser>> getFollowings();

    List<Ref<? extends ITweet>> getTimeline();

    void addFollower(Ref<? extends IUser> follower);

    void addFollowing(Ref<? extends IUser> following);

    void removeFollower(Ref<? extends IUser> follower);

    void removeFollowing(Ref<? extends IUser> following);

    @Transactional
    void addRetweet(Ref<? extends ITweet> tweet);

    @Transactional
    void addToTimeline(Ref<? extends ITweet> tweet);
}
