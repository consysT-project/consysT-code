package de.tuda.stg.consys.core.store.cassandra.backend.trigger

import com.datastax.oss.driver.api.core.`type`.codec.TypeCodecs
import de.tuda.stg.consys.core.store.cassandra.backend.CassandraReplicaAdapter
import de.tuda.stg.consys.core.store.utils.Reflect
import org.json.{JSONArray, JSONObject}
import de.tuda.stg.consys.core.store.Triggerable
import java.lang.reflect.Field

object RMIServer extends RMIServerInterface {

  private final val TYPE_FIELD = 1
  private final val TYPE_OBJECT = 2

  def trigger(data: String): Unit = {
    println("\u001b[34m " + data + "\u001b[0m")

    /* Create JSON Object out of the passed data */
    val jsonObject: JSONObject = new JSONObject(data)

    /* Extract the rows */
    val rows: JSONArray = jsonObject.getJSONArray("rows")

    /* Map to store extracted data */
    var fields: Map[Field, Serializable] = Map.empty
    var address: String = ""
    var clazz: String = ""

    /* Loop over all the rows */
    for (i <- 0 until rows.length) {
      val row: JSONObject = rows.getJSONObject(i)
      address = row.get("partitionKey").asInstanceOf[String]
      val cells: JSONArray = row.getJSONArray("cells")
      val fieldType: String = extractCell(cells, "type")

      if (fieldType.toInt == TYPE_FIELD) {
        clazz = extractCell(cells, "class")
        val clusteringKey: String = row.get("clusteringKey").asInstanceOf[String]
        val state: String = extractCell(cells, "state")

        val field: Field = Reflect.getField(Class.forName(clazz), clusteringKey)

        /* Store extracted data in a map */
        fields += (field -> deserialize(state))

      } else if (fieldType.toInt == TYPE_OBJECT) {
        handleObjectEntryTrigger(cells)
      } else {
        throw new Exception(s"Entry with the address: ${address} has an unknown field type.")
      }
    }

    if (fields.nonEmpty) {
      handleFieldEntryTrigger(fields, clazz)
    }
  }

  /**
   * Handles the trigger event for object entries in Cassandra.
   * @param cells: JSONArray containing the cells of the triggered row in Cassandra
   */
  def handleObjectEntryTrigger(cells: JSONArray): Unit = {
    val state: String = extractCell(cells, "state")
    val instance = deserialize(state)
    runTrigger(instance);
  }

  /**
   * Handles the trigger event for field entries in Cassandra.
   *
   * @param instance
   */
  def handleFieldEntryTrigger(fields: Map[Field, Serializable], clazz: String): Unit = {
    val constructor = Reflect.getConstructor(Class.forName(clazz))
    val instance = constructor.newInstance()

    fields.foreach(entry => {
      val field = Reflect.getField(Class.forName(clazz), entry._1.getName)
      field.setAccessible(true)
      field.set(instance, entry._2)
    })

    runTrigger(instance)
  }

  def runTrigger(instance: Any): Unit = {
    if (instance.isInstanceOf[Triggerable]) {
      val triggerableObj = instance.asInstanceOf[Triggerable]
      triggerableObj.onTrigger()
    }
  }

  def deserialize(data: String): Serializable = {
    val byteBuffer = TypeCodecs.BLOB.parse("0x" + data)
    CassandraReplicaAdapter.deserializeObject[Serializable](byteBuffer)
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
