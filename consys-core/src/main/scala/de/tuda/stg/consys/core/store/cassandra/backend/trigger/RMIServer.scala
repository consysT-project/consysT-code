package de.tuda.stg.consys.core.store.cassandra.backend.trigger

import com.datastax.oss.driver.api.core.`type`.codec.TypeCodecs
import de.tuda.stg.consys.core.store.cassandra.CassandraStore
import de.tuda.stg.consys.core.store.cassandra.backend.CassandraReplicaAdapter
import de.tuda.stg.consys.core.store.utils.Reflect
import org.json.{JSONArray, JSONObject}
import com.datastax.oss.driver.api.core.{ConsistencyLevel => CassandraLevel}
import de.tuda.stg.consys.core.store.Triggerable
import java.lang.reflect.Field

class RMIServer(cassandraReplicaAdapter: CassandraReplicaAdapter) extends RMIServerInterface {

  private final val TYPE_FIELD = 1
  private final val TYPE_OBJECT = 2

  def trigger(data: String): Unit = {
    println("\u001b[34m " + data + "\u001b[0m")

    /* Create JSON Object out of the passed data */
    val jsonObject: JSONObject = new JSONObject(data)

    /* Extract the rows */
    val rows: JSONArray = jsonObject.getJSONArray("rows")

    /* Map to store extracted data */
    var dataMap: Map[Field, String] = Map.empty
    var address: String = ""

    /* Loop over all the rows */
    for (i <- 0 until rows.length) {
      val row: JSONObject = rows.getJSONObject(i)
      address = row.get("partitionKey").asInstanceOf[String]
      val cells: JSONArray = row.getJSONArray("cells")
      val fieldType: String = extractCell(cells, "type")

      if (fieldType.toInt == TYPE_FIELD) {
        val clazz = cassandraReplicaAdapter.classMap(address)
        val clusteringKey: String = row.get("clusteringKey").asInstanceOf[String]
        val state: String = extractCell(cells, "state")

        val field: Field = Reflect.getField(clazz, clusteringKey)

        /* Store extracted data in the map */
        dataMap += (field -> state)

      } else if (fieldType.toInt == TYPE_OBJECT) {
        handleObjectEntryTrigger(cells)
      }
    }

    handleFieldEntryTrigger(address, dataMap)
  }

  /**
   * Handles the trigger event for object entries in Cassandra.
   * @param cells: JSONArray containing the cells of the triggered row in Cassandra
   */
  def handleObjectEntryTrigger(cells: JSONArray): Unit = {
    /* Extract the state value from the cells, parse it into a ByteBuffer and deserialize */
    val stateValue: String = extractCell(cells, "state")
    val byteBuffer = TypeCodecs.BLOB.parse("0x" + stateValue);
    val instance = CassandraReplicaAdapter.deserializeObject[Serializable](byteBuffer)

    runTrigger(instance);
  }

  /**
   * Handles the trigger event for field entries in Cassandra.
   *
   * @param address: the address (partition key) of the triggered field entry in Cassandra
   * @param dataMap: a map containing the fields and their corresponding values
   */
  def handleFieldEntryTrigger(address: String, dataMap: Map[Field, String]): Unit = {
    /* Get the class of the object stored at the specified address */
    val clazz = cassandraReplicaAdapter.classMap(address)

    /* Read the stored field entry from Cassandra */
    val storedFieldEntry = cassandraReplicaAdapter.readFieldEntry[CassandraStore#ObjType](address, CassandraLevel.ALL, Some(clazz))
    var mergedFields = storedFieldEntry.fields

    /* Merge dataMap entries with read entries */
    for ((field, value) <- dataMap) {
      val byteBuffer = TypeCodecs.BLOB.parse("0x" + value);
      val deserializedValue = CassandraReplicaAdapter.deserializeObject[Serializable](byteBuffer);
      mergedFields = mergedFields + (field -> deserializedValue)
    }

    /* Create a new instance of the class and fill it with data */
    val constr = Reflect.getConstructor(clazz)
    val instance = constr.newInstance()

    mergedFields.foreach(entry => {
      val field = Reflect.getField(clazz, entry._1.getName)
      field.setAccessible(true)
      field.set(instance, entry._2)
    })

    runTrigger(instance);
  }

  def runTrigger(instance: Any): Unit = {
    if (instance.isInstanceOf[Triggerable]) {
      val triggerableObj = instance.asInstanceOf[Triggerable]
      triggerableObj.onTrigger()
    }
  }

  /**
   * Extracts a cell value from a JSONArray
   *
   * @param cells The JSONArray to extract the cell from
   * @param cell  The name of the cell to extract
   * @return The value of the extracted cell as a string, prefixed with "0x"
   */
  private def extractCell(cells: JSONArray, cellName: String): String = {
    var value: String = ""
    for (i <- 0 until cells.length) {
      val cell = cells.getJSONObject(i)
      if (cell.getString("name").equals(cellName)) {
        value = cell.getString("value")
      }
    }
    value
  }

}
