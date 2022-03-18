package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.*;

public class Group implements Serializable {
    private final String id;
    private String name;
    private String description;
    private boolean requiresJoinConfirmation;
    private final Map<String, Ref<User>> owners;
    private final Map<String, Ref<User>> members;
    private final Map<String, Ref<User>> pendingMembers;
    private final List<Ref<? extends Post>> feed;

    public Group(String id, String name, String description, boolean requiresJoinConfirmation, Ref<User> owner) {
        this.id = id;
        this.name = name;
        this.description = description;
        this.requiresJoinConfirmation = requiresJoinConfirmation; // TODO
        this.owners = new HashMap<>();
        this.owners.put(owner.ref().getId(), owner);
        this.members = new HashMap<>();
        this.pendingMembers = new HashMap<>();
        this.feed = new LinkedList<>();
    }

    public void addPost(Ref<? extends Post> activity) {
        feed.add(0, activity);
        // TODO: should group posts be added to the personal feed of members?
        //for (Ref<User> member : members.values())
        //    member.ref().addActivity(activity);
        //for (Ref<User> owner : owners.values())
        //    owner.ref().addActivity(activity);
    }

    @Transactional
    public boolean isUserInGroup(Ref<User> user) {
        return members.containsKey(user.ref().getId()) || owners.containsKey(user.ref().getId());
    }

    @Transactional
    public boolean isOwner(Ref<User> user) {
        return owners.containsKey(user.ref().getId());
    }

    @StrongOp
    @Transactional
    public void join(Ref<User> user) {
        if (!requiresJoinConfirmation) {
            members.put(user.ref().getId(), user);
        } else {
            pendingMembers.put(user.ref().getId(), user);
        }
    }

    @Transactional
    public void acceptMembershipRequest(Ref<User> user, Ref<User> sessionUser) {
        if (isOwner(sessionUser)) {
            throw new IllegalArgumentException("user is not privileged to accept membership requests");
        }

        if (pendingMembers.remove(user.ref().getId()) != null) {
            members.put(user.ref().getId(), user);
        } else {
            throw new IllegalArgumentException("user has not requested membership");
        }
    }

    @Transactional
    public void promoteToOwner(Ref<User> member) {
        if (members.remove(member.ref().getId()) != null) {
            owners.put(member.ref().getId(), member);
        } else {
            throw new IllegalArgumentException("user is not member of group");
        }
    }

    @Transactional
    public void removeOwner(Ref<User> user) {
        this.owners.remove(user.ref().getId());
    }

    public void setName(String name) {
        this.name = name;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    public void setRequiresJoinConfirmation(boolean requiresJoinConfirmation) {
        this.requiresJoinConfirmation = requiresJoinConfirmation;
    }

    public String getId() {
        return id;
    }

    public String getName() {
        return name;
    }

    public String getDescription() {
        return description;
    }

    public boolean isRequiresJoinConfirmation() {
        return requiresJoinConfirmation;
    }

    public List<Ref<User>> getOwners() {
        return new ArrayList<>(owners.values());
    }

    public List<Ref<User>> getMembers() {
        return new ArrayList<>(members.values());
    }

    public List<Ref<? extends Post>> getFeed() {
        return feed;
    }
}
