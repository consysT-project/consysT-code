## Troubleshooting

#### Security Policy (RMI errors)

1. Create a file named **"java.policy"** in the directory **"$JAVA_HOME/lib/security"**:

```
grant {
  permission java.security.AllPermission;
};
```

2. To set the policy for the project in Intellj IDEA:

- Press **"CTRL + Shift + A"**
- Search for **"Edit configurations"** and launch it
- Select **"Modify Options"** and **"Add VM Options"**
- In the new input field, add the following option:
  `-Djava.security.policy=file:/usr/lib/jvm/$JAVA_HOME/lib/security/java.policy`
- Click "OK"

---

Remarks:

- `System.setProperty("java.security.policy", "file:/usr/lib/jvm/$JAVA_HOME/lib/security/java.policy")` to set the policy manually in code
- InteractiveSession.java - background task turned off, only one replica running
