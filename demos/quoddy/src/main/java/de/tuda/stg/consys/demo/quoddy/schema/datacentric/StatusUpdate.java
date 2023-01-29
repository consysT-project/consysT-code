package de.tuda.stg.consys.demo.quoddy.schema.datacentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.quoddy.schema.Comment;
import de.tuda.stg.consys.demo.quoddy.schema.IStatusUpdate;
import de.tuda.stg.consys.demo.quoddy.schema.IUser;
import de.tuda.stg.consys.japi.Ref;

import java.util.List;
import java.util.UUID;


public @Weak class StatusUpdate extends Post implements IStatusUpdate {
    private String text = "";

    public StatusUpdate(@Local @Immutable UUID id, Ref<? extends IUser> owner, @Weak @Mutable String text) {
        super(id, owner);
        this.text = text;
    }

    public void setText(@Weak @Mutable String text) {
        this.text = text;
    }

    public String getText() {
        return text;
    }

    @SuppressWarnings({"consistency"}) // TODO: compiler problems
    @Override
    @Transactional
    public String toString() {
        @Mutable @Weak String commentSection = "";
        @Immutable @Weak List<Comment> comments = getComments();
        for (int i = 0; (@Weak boolean)(i < Math.min(comments.size(), 5)); i++) {
            commentSection += "\nBy " + comments.get(i).getOwner().ref().getName() + ": " + comments.get(i).getText();
        }
        return "Posted by " + getOwner() + " on " + getCreationTimestamp() + ": " + getText() +
                "\n Comments: " + commentSection;
    }
}
