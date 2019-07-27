package de.tuda.stg.consys.casestudyakka;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.*;
import java.util.LinkedList;

public class AWSTest implements Serializable {

    public static void main(String[] args) throws Exception {


        String path = args[0];
        String currLine;
        LinkedList<String> fileCont = new LinkedList<String>();

        try {
            FileReader fileReader =
                    new FileReader(path);

            BufferedReader bufferedReader =
                    new BufferedReader(fileReader);

            while((currLine = bufferedReader.readLine()) != null) {
                fileCont.add(currLine);
            }

            bufferedReader.close();
        }
        catch(FileNotFoundException ex) {
            System.out.println(
                    "Unable to open file '" +
                            path + "'");
            System.exit(0);
        }
        catch(IOException ex) {
            System.out.println(
                    "Error reading file '"
                            + path + "'");
            System.exit(0);
        }

        int replicaCount = fileCont.size();
        thisHost = fileCont.remove();
        String thisHostName = thisHost.split(";")[0];
        int thisPort = Integer.parseInt(thisHost.split(";")[1]);

        //Setup the replica systems
        //JReplicaSystem[] systems = new JReplicaSystem[replicaCount];
        thisSystem = JReplicaSystem.fromActorSystem(thisHostName, thisPort);
        ///thisSystem = JReplicaSystem.fromActorSystem(thisPort);
        System.out.println("Created Replica System from " + thisHost);
        for (String otherHost: fileCont) {
            String otherHostName = otherHost.split(";")[0];
            int otherPort = Integer.parseInt(otherHost.split(";")[1]);
            thisSystem.addReplicaSystem(otherHostName, otherPort);
            System.out.println("Added Replica System from " + otherHost);
        }

        //Try to set the value
        setValue();

        BufferedReader reader =
                new BufferedReader(new InputStreamReader(System.in));

        //Do the user input thing
        while(true){
            String input = reader.readLine();
            switch (input){
                case "exit":
                    System.out.println("Shutting down");
                    System.exit(0);
                case "read":
                    System.out.println((String) value.getField("content"));
                    break;
                case "write":
                    value.setField("content", thisHost);
                    System.out.println("Field has been set");
                    break;
                default:
                    break;
            }
        }

    }
    static String thisHost;

    static JReplicaSystem thisSystem;

    static JRef<@Strong Container> value;


    private static void setValue(){
        try{
            value = thisSystem.replicate("valueString", new Container("from " + thisHost), JConsistencyLevel.STRONG);

        }catch (Exception e){
            value = thisSystem.ref("valueString", Container.class, JConsistencyLevel.STRONG);
        }
    }

    static class Container implements Serializable{
        public String content;

        public Container(String cont){
            content = cont;
        }
    }
}
