package de.tuda.stg.consys.demo.docshare;

import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.demo.docshare.schema.opcentric.Document;
import de.tuda.stg.consys.demo.docshare.schema.opcentric.User;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import org.json.JSONException;
import org.json.JSONObject;
import scala.Function1;
import scala.Option;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.MIXED;
import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.STRONG;

@SuppressWarnings({"consistency"})
public class Session {
    private CassandraStoreBinding store;
    private Ref<User> user;
    public static ConsistencyLevel<CassandraStore> documentConsistencyLevel;
    public static ConsistencyLevel<CassandraStore> userConsistencyLevel;
    private <U> Option<U> doTransaction(Function1<CassandraTransactionContextBinding, Option<U>> code) {
        return store.transaction(code::apply);
    }

    public Session(@Mutable CassandraStoreBinding store) {
        this.store = store;
    }

    public void init() {
        this.user = doTransaction(
                ctx -> Option.apply(ctx.replicate("user", userConsistencyLevel, User.class))).get();
    }

    public void initUser(String id) {
        this.user = doTransaction(
                ctx -> Option.apply(ctx.replicate("user:" + id, userConsistencyLevel, User.class))).get();
    }

    public void addDocument(String title) {
        doTransaction(ctx -> Option.apply(ctx.replicate(title, documentConsistencyLevel, Document.class, title))).get();
    }

    public void addDocument(String id, String title) {
        doTransaction(ctx -> Option.apply(ctx.replicate("document:" + id, documentConsistencyLevel, Document.class, title))).get();
    }

    public void editDocument(String title, String content, String description) {
        doTransaction(ctx -> {
            Ref<Document> documentRef = ctx.lookup(title, documentConsistencyLevel, Document.class);
            user.ref().editDocumentContent(documentRef, content);
            user.ref().editDocumentDescription(documentRef, description);
            return Option.apply(documentRef);
        }).get();
    }

    public void editDocumentContent(Ref<Document> document, String content) {
        doTransaction(ctx -> {
            user.ref().editDocumentContent(document, content);
            return Option.apply(document);
        }).get();
    }

    public void editDocumentDescription(Ref<Document> document, String description) {
        doTransaction(ctx -> {
            user.ref().editDocumentDescription(document, description);
            return Option.apply(document);
        }).get();
    }


    public JSONObject readDocument(String title) {

        JSONObject jsonObject = doTransaction(ctx -> {
            Ref<Document> documentRef = ctx.lookup(title, documentConsistencyLevel, Document.class);

            JSONObject jsonObjectTmp = new JSONObject();

            try {
                jsonObjectTmp.put("type", "readDocument");
                jsonObjectTmp.put("title", documentRef.ref().getTitle());
                jsonObjectTmp.put("content", documentRef.ref().getContent());
                jsonObjectTmp.put("description", documentRef.ref().getDescription());
            } catch (JSONException e) {
                throw new RuntimeException(e);
            }
            return Option.apply(jsonObjectTmp);
        }).get();

        return jsonObject;
    }

    public Ref<? extends @Mutable User> findUser(String id) {
        return doTransaction(ctx -> Option.apply(ctx.lookup("user:" + id, userConsistencyLevel, User.class))).get();
    }

    public Ref<? extends @Mutable Document> findDocument(String id) {
        return doTransaction(ctx -> Option.apply(ctx.lookup("document:" + id, documentConsistencyLevel, Document.class))).get();
    }

}
