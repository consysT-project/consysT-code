package de.tuda.stg.consys.core.store.cassandra.backend

import org.apache.cassandra.db.{Clustering, Mutation}
import org.apache.cassandra.db.partitions.Partition
import org.apache.cassandra.db.rows.{Cell, Row, Unfiltered, UnfilteredRowIterator}
import org.apache.cassandra.schema.ColumnMetadata
import org.apache.cassandra.triggers.ITrigger
import org.json.{JSONException, JSONObject}

import java.nio.ByteBuffer
import java.rmi.{Remote, RemoteException}
import java.rmi.registry.{LocateRegistry, Registry}
import java.util
import java.util.Collections
import scala.collection.convert.ImplicitConversions.`collection asJava`


/*
class CassandraReplicaTrigger extends ITrigger {
  override def augment(partition: Partition): util.Collection[Mutation] = {
    val jsonObject: JSONObject = new JSONObject
    val it: UnfilteredRowIterator = partition.unfilteredIterator
    while (it.hasNext) {
      val item: Unfiltered = it.next
      if (item.isRow) {
        val clustering: Clustering[_] = item.clustering.asInstanceOf[Clustering[_]]
        // TODO: Find out why reading the partition key leads to a duplication of the entry in the DB table
        //ByteBuffer partitionKeyBB = partition.partitionKey().getKey();
        //String partitionKey = Charset.defaultCharset().decode(partitionKeyBB).toString();
        val clusteringKey: String = clustering.toCQLString(partition.metadata)
        try
          //jsonObject.put("partitionKey", partitionKey);
          jsonObject.put("clusteringKey", clusteringKey)
        catch {
          case e: JSONException =>
            throw new RuntimeException(e)
        }
        val row: Row = partition.getRow(clustering)
        val cells: util.Iterator[Cell[_]] = row.cells.iterator
        val columns: util.Iterator[ColumnMetadata] = row.columns.iterator
        val cellObjects: util.ArrayList[JSONObject] = new util.ArrayList[JSONObject]
        while (cells.hasNext && columns.hasNext) {
          val jsonCell: JSONObject = new JSONObject
          val columnDef: ColumnMetadata = columns.next
          val cell: Cell[_] = cells.next
          try {
            jsonCell.put("name", columnDef.name.toString)
            jsonCell.put("value", columnDef.`type`.getString(cell.value.asInstanceOf[ByteBuffer]))
          } catch {
            case e: JSONException =>
              throw new RuntimeException(e)
          }
          cellObjects.add(jsonCell)
        }
        try jsonObject.put("cells", cellObjects)
        catch {
          case e: JSONException =>
            throw new RuntimeException(e)
        }
      }
    }
    // Send data
    try {
      val registry: Registry = LocateRegistry.getRegistry(1234)
      val server: RMIServerInterface = registry.lookup("rmi://127.0.0.1:1234/test").asInstanceOf[RMIServerInterface]
      server.print(jsonObject.toString)
    } catch {
      case e: Exception =>
        System.err.println("Client exception: " + e.toString)
        e.printStackTrace()
    }
    return Collections.emptyList
  }
}
*/

