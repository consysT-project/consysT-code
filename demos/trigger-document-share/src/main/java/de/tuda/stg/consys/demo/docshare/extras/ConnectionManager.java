package de.tuda.stg.consys.demo.docshare.extras;

import org.checkerframework.dataflow.qual.SideEffectFree;
import org.java_websocket.WebSocket;
import org.json.JSONException;
import org.json.JSONObject;

import java.util.HashSet;
import java.util.Set;

public class ConnectionManager {
        private static Set<WebSocket> conns = new HashSet<>();

        public static void addConnection(WebSocket conn) {
            conns.add(conn);
        }

        public static void removeConnection(WebSocket conn) {
            conns.remove(conn);
        }

        @SideEffectFree
        public static void showNotification() {
            JSONObject jsonObject = new JSONObject();

            try {
                jsonObject.put("type", "trigger");
            } catch (JSONException e) {
                throw new RuntimeException(e);
            }

            for (WebSocket conn : conns) {
                conn.send(jsonObject.toString());
            }
        }
}
