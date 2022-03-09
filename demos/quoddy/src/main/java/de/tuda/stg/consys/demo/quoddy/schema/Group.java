package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;

public class Group implements Serializable {
    private final String id;
    private String name;
    private String description;
    private boolean requiresJoinConfirmation;
    private final List<Ref<User>> owners;
    private final List<Ref<User>> members;
    private final List<Ref<User>> pendingMembers;
    private final List<Ref<? extends Activity>> feed;

    public Group(String id, String name, String description, boolean requiresJoinConfirmation, Ref<User> owner) {
        this.id = id;
        this.name = name;
        this.description = description;
        this.requiresJoinConfirmation = requiresJoinConfirmation; // TODO
        this.owners = new LinkedList<>();
        this.owners.add(owner);
        this.members = new LinkedList<>();
        this.pendingMembers = new LinkedList<>();
        this.feed = new LinkedList<>();
    }

    public void addActivity(Ref<? extends Activity> activity) {
        feed.add(0, activity);
        // TODO: should group posts be added to the personal feed of members?
        for (Ref<User> member : members)
            member.ref().addActivity(activity);
        for (Ref<User> owner : owners)
            owner.ref().addActivity(activity);
    }

    @Transactional
    public boolean isUserInGroup(Ref<User> user) {
        boolean result = false;
        for (Ref<User> member : members)
            result |= Util.equalsUser(user, member);
        for (Ref<User> owner : owners)
            result |= Util.equalsUser(user, owner);
        return result;
    }

    public void join(Ref<User> user) {
        if (!requiresJoinConfirmation) {
            members.add(user);
        } else {
            pendingMembers.add(user);
        }
    }

    @Transactional
    public void acceptMembershipRequest(Ref<User> user, Ref<User> sessionUser) {
        if (owners.stream().noneMatch(x -> Util.equalsUser(x, sessionUser))) {
            throw new IllegalArgumentException("user is not privileged to accept membership requests");
        }

        if (pendingMembers.removeIf(x -> Util.equalsUser(x, user))) {
            members.add(user);
        } else {
            throw new IllegalArgumentException("user has not requested membership");
        }
    }

    @Transactional
    public void promoteToOwner(Ref<User> member) {
        if (members.removeIf(x -> Util.equalsUser(x, member))) {
            owners.add(member);
        } else {
            throw new IllegalArgumentException("user is not member of group");
        }
    }

    @Transactional
    public void removeOwner(Ref<User> user) {
        this.owners.removeIf(x -> Util.equalsUser(x, user));
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
        return owners;
    }

    public List<Ref<User>> getMembers() {
        return members;
    }

    public List<Ref<? extends Activity>> getFeed() {
        return feed;
    }
}
