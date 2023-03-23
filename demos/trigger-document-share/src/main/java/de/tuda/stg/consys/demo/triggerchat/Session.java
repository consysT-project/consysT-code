package de.tuda.stg.consys.demo.triggerchat;

import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.demo.triggerchat.schema.opcentric.Document;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import org.json.JSONException;
import org.json.JSONObject;
import scala.Function1;
import scala.Option;

import java.util.Collection;
import java.util.List;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.MIXED;

@SuppressWarnings({"consistency"})
public class Session {
    private CassandraStoreBinding store;

    public static ConsistencyLevel<CassandraStore> consistencyLevel = MIXED;
    private <U> Option<U> doTransaction(Function1<CassandraTransactionContextBinding, Option<U>> code) {
        return store.transaction(code::apply);
    }

    public Session(@Mutable CassandraStoreBinding store) {
        this.store = store;
    }

    public void addDocument(String title) {
        doTransaction(ctx -> Option.apply(ctx.replicate(title, consistencyLevel, Document.class, title))).get();
    }

    public void saveDocument(String title, String content) {

        doTransaction(ctx -> {
            Ref<Document> documentRef = ctx.lookup(title, consistencyLevel, Document.class);
            documentRef.ref().save(content);
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
            } catch (JSONException e) {
                throw new RuntimeException(e);
            }
            return Option.apply(jsonObjectTmp);
        }).get();

        return jsonObject;
    }

}
