package de.tuda.stg.consys.demo.triggerchat;

import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.demo.triggerchat.schema.opcentric.Document;
import de.tuda.stg.consys.demo.triggerchat.schema.opcentric.User;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import org.checkerframework.dataflow.qual.SideEffectFree;
import org.java_websocket.WebSocket;
import org.json.JSONException;
import org.json.JSONObject;
import scala.Function1;
import scala.Option;

import javax.print.Doc;
import java.io.Serializable;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.MIXED;

@SuppressWarnings({"consistency"})
public class Session {
    private CassandraStoreBinding store;

    private Ref<User> user;

    public static ConsistencyLevel<CassandraStore> consistencyLevel = MIXED;
    private <U> Option<U> doTransaction(Function1<CassandraTransactionContextBinding, Option<U>> code) {
        return store.transaction(code::apply);
    }

    public Session(@Mutable CassandraStoreBinding store) {
        this.store = store;
    }

    public void init() {
        this.user = doTransaction(
                ctx -> Option.apply(ctx.replicate("user", consistencyLevel, User.class))).get();
    }

    public void addDocument(String title) {
        doTransaction(ctx -> Option.apply(ctx.replicate(title, consistencyLevel, Document.class, title))).get();
    }

    public void editDocument(String title, String content, String description) {
        doTransaction(ctx -> {
            Ref<Document> documentRef = ctx.lookup(title, consistencyLevel, Document.class);
            user.ref().editDocumentContent(documentRef, content);
            user.ref().editDocumentDescription(documentRef, description);
            return Option.apply(documentRef);
        }).get();
    }


    public JSONObject readDocument(String title) {

        JSONObject jsonObject = doTransaction(ctx -> {
            Ref<Document> documentRef = ctx.lookup(title, consistencyLevel, Document.class);

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

}
