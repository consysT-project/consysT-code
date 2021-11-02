package demos.message.java;

import java.io.Serializable;
import java.util.Objects;

public class Group implements Serializable {

    public final User[] users = new User[100];

    public void addPost(String msg) {
        for (User user : users) {
            if (user != null) user.send(msg);
        }
    }

    public void addUser(User user) {
        for (int i = 0; i < users.length; i++) {
            if (users[i] == null) {
                users[i] = user;
                return;
            }
        }
        throw new IllegalArgumentException("no space for users");
    }

    public User getUser(int index) {
        User user = users[index];
        Objects.requireNonNull(user, "no user at index " + index);

        return user;
    }
}
