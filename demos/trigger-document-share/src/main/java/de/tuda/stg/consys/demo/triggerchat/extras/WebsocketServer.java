package de.tuda.stg.consys.demo.triggerchat.extras;

import de.tuda.stg.consys.demo.triggerchat.Session;
import de.tuda.stg.consys.demo.triggerchat.schema.opcentric.Document;
import de.tuda.stg.consys.japi.Ref;
import org.java_websocket.WebSocket;
import org.java_websocket.handshake.ClientHandshake;
import org.java_websocket.server.WebSocketServer;
import org.json.JSONException;
import org.json.JSONObject;

import java.net.InetSocketAddress;
import java.nio.ByteBuffer;
import java.util.*;

public class WebsocketServer extends WebSocketServer {

    private static int TCP_PORT = 9999;
    private Session[] sessions;

    private int sessionsNumber = 3;
    private Set<WebSocket> conns;

    public WebsocketServer(Session[] sessions) {
        super(new InetSocketAddress(TCP_PORT));
        this.sessions = sessions;
        conns = new HashSet<>();
    }

    @Override
    public void onOpen(WebSocket conn, ClientHandshake handshake) {
        conns.add(conn);
        System.out.println("New connection from " + conn.getRemoteSocketAddress().getAddress().getHostAddress());


    }

    @Override
    public void onClose(WebSocket conn, int code, String reason, boolean remote) {
        conns.remove(conn);
        System.out.println("Closed connection to " + conn);
    }

    @Override
    public void onMessage(WebSocket conn, String message) {
        System.out.println("Message from client: " + message);

        List<WebSocket> cons = new ArrayList<>(conns);
        int sessionId = cons.indexOf(conn) % sessionsNumber;

        try {
            JSONObject jsonObject = new JSONObject(message);

            String type = jsonObject.getString("type");
            String title = jsonObject.getString("title");

            switch (type) {
                case "createDocument": {
                    handleCreateDocument(title, sessionId);
                    break;
                }
                case "readDocument": {
                    handleReadDocument(title, sessionId, conn);
                    break;
                }
                case "saveDocument": {
                    String content = jsonObject.getString("content");
                    handleSaveDocument(title, sessionId, content);
                    break;
                }
                case "runSimulation": {
                    handleSimulation(title, 1, conn);
                    break;
                }
                default: {
                    System.out.println("Unknown message type.");
                    break;
                }
            }
        } catch (JSONException e) {
            throw new RuntimeException(e);
        }
    }

    public void handleCreateDocument(String title, int sessionId) {
        sessions[sessionId].addDocument(title);
    }

    public void handleReadDocument(String title, int sessionId, WebSocket conn) {
        JSONObject jsonObject = sessions[sessionId].readDocument(title);
        conn.send(jsonObject.toString());
    }

    public void handleSaveDocument(String title, int sessionId, String content) {
        sessions[sessionId].saveDocument(title, content);
    }

    public void handleSimulation(String title, int sessionId, WebSocket conn) {
        //sessions[sessionId].runSimulation(title, conn);
    }


    @Override
    public void onError(WebSocket conn, Exception ex) {
        ex.printStackTrace();
        if (conn != null) {
            conns.remove(conn);
        }
        System.out.println("ERROR from " + conn.getRemoteSocketAddress().getAddress().getHostAddress());
    }

    @Override
    public void onStart() {
        System.out.println("On start");
    }
}