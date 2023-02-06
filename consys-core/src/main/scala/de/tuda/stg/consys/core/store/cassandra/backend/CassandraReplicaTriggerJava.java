package de.tuda.stg.consys.core.store.cassandra.backend;

import de.tuda.stg.consys.core.store.cassandra.backend.trigger.RMIServerInterface;
import org.apache.cassandra.db.Clustering;
import org.apache.cassandra.db.Mutation;
import org.apache.cassandra.db.partitions.Partition;
import org.apache.cassandra.db.rows.Cell;
import org.apache.cassandra.db.rows.Row;
import org.apache.cassandra.db.rows.Unfiltered;
import org.apache.cassandra.db.rows.UnfilteredRowIterator;
import org.apache.cassandra.schema.ColumnMetadata;
import org.apache.cassandra.triggers.ITrigger;
import org.json.JSONException;
import org.json.JSONObject;

import java.nio.ByteBuffer;
import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;
import java.util.*;
public class CassandraReplicaTriggerJava implements ITrigger {

    @Override
    public Collection<Mutation> augment(Partition partition) {
        JSONObject jsonObject = new JSONObject();
        UnfilteredRowIterator it = partition.unfilteredIterator();

        List<JSONObject> rows = new ArrayList<>();

        while (it.hasNext()) {
            Unfiltered item = it.next();

            if (item.isRow()) {
                Clustering clustering = (Clustering) item.clustering();

                JSONObject jsonRow = new JSONObject();

                String partitionKey = "";

                try {
                    ByteBuffer buffer = partition.partitionKey().getKey();
                    partitionKey = new String(buffer.array(), "UTF-8");
                } catch (Exception ex) {
                    System.out.println(ex);
                }

                String clusteringKey = clustering.toCQLString(partition.metadata());

                try {
                    jsonRow.put("partitionKey", partitionKey);
                    jsonRow.put("clusteringKey", clusteringKey);
                } catch (JSONException e) {
                    throw new RuntimeException(e);
                }


                Row row = partition.getRow(clustering);

                Iterator<Cell<?>> cells = row.cells().iterator();
                Iterator<ColumnMetadata> columns = row.columns().iterator();

                List<JSONObject> cellObjects = new ArrayList<>();


                while (cells.hasNext() && columns.hasNext()) {
                    JSONObject jsonCell = new JSONObject();

                    ColumnMetadata columnDef = columns.next();
                    Cell cell = cells.next();

                    try {
                        jsonCell.put("name", columnDef.name.toString());
                        jsonCell.put("value", columnDef.type.getString((ByteBuffer) cell.value()));
                    } catch (JSONException e) {
                        throw new RuntimeException(e);
                    }
                    cellObjects.add(jsonCell);
                }
                try {
                    jsonRow.put("cells", cellObjects);
                } catch (JSONException e) {
                    throw new RuntimeException(e);
                }

                rows.add(jsonRow);
            }
        }

        try {
            jsonObject.put("rows", rows);
        } catch (JSONException e) {
            throw new RuntimeException(e);
        }

        // Send data
        try {
            Thread t = new Thread(new Runnable() {
                public void run() {
                    try {
                        Registry registry = LocateRegistry.getRegistry(1234);
                        RMIServerInterface server = (RMIServerInterface) registry.lookup("rmi://127.0.0.1:1234/test");
                        server.trigger(jsonObject.toString());
                    } catch (Exception e) {
                        e.printStackTrace();
                    }
                }
            });

            t.start();
        } catch (Exception e) {
            System.err.println("Client exception: " + e.toString());
            e.printStackTrace();
        }

        return Collections.emptyList();
    }

}
