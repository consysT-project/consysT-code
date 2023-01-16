package de.tuda.stg.consys.core.store.cassandra.backend;

import org.apache.cassandra.db.Clustering;
import org.apache.cassandra.db.Mutation;
import org.apache.cassandra.db.partitions.Partition;
import org.apache.cassandra.db.rows.Cell;
import org.apache.cassandra.db.rows.Row;
import org.apache.cassandra.db.rows.Unfiltered;
import org.apache.cassandra.db.rows.UnfilteredRowIterator;
import org.apache.cassandra.schema.ColumnMetadata;
import org.apache.cassandra.triggers.ITrigger;

import java.nio.ByteBuffer;
import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;

public class CassandraReplicaTriggerJava implements ITrigger {

    @Override
    public Collection<Mutation> augment(Partition partition) {
        // Extract data
        String clusteringKey = "";
        String columnName = "";
        String value = "";

        UnfilteredRowIterator it = partition.unfilteredIterator();

        while (it.hasNext()) {
            Unfiltered item = it.next();

            if (item.isRow()) {
                Clustering clustering = (Clustering) item.clustering();
                clusteringKey = clustering.toCQLString(partition.metadata());
                Row row = partition.getRow(clustering);

                Iterator<Cell<?>> cells = row.cells().iterator();
                Iterator<ColumnMetadata> columns = row.columns().iterator();

                while (cells.hasNext() && columns.hasNext()) {
                    ColumnMetadata columnDef = columns.next();
                    Cell cell = cells.next();

                    columnName = columnDef.name.toString();
                    value = columnDef.type.getString((ByteBuffer) cell.value());
                }
            }
        }

        DataObject dataObject = new DataObject(clusteringKey, columnName, value);

        // Send data
        try {
            Registry registry = LocateRegistry.getRegistry(1234);
            RMIServerInterface server = (RMIServerInterface) registry.lookup("rmi://127.0.0.1:1234/test");
            server.print(dataObject);
        } catch (Exception e) {
            System.err.println("Client exception: " + e.toString());
            e.printStackTrace();
        }

        return Collections.emptyList();
    }
}
