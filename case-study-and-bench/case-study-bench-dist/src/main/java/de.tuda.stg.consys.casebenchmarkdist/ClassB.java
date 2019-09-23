package de.tuda.stg.consys.casebenchmarkdist;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.BufferedReader;
import java.io.InputStreamReader;

public class ClassB {
    public static void main(String[] args) throws Exception {
        int thisPort = 2553;
        //Setup the replica systems
        thisSystem = JReplicaSystem.fromActorSystem(thisPort);
        System.out.println("Created Replica System from 127.0.0.1");
        boolean cont = true;

        while(cont){
            try{
                thisSystem.addReplicaSystem("127.0.0.1", 2552);
                System.out.println("Added Replica System from 127.0.0.1 ");
                cont = false;
            }
            catch(Exception e){
                System.out.println("Could not add Replica System");
            }

            Thread.sleep(1000);
        }
        System.out.println("Added Other Replica");

        //Try to set the value
        setValue();

        //Trying to sync the ref or invoking something on it causes an error
        //value.sync();


        BufferedReader reader =
                new BufferedReader(new InputStreamReader(System.in));

        //Do the user input thing
        while(true){
            String input = reader.readLine();
            String[] inputSplit = input.split(":");
            switch (inputSplit[0]){
                case "exit":
                    System.out.println("Shutting down");
                    thisSystem.close();
                    System.exit(0);
                case "read":
                    System.out.println((String) value.getField("content"));
                    break;
                case "write":
                    value.setField("content", inputSplit[1]);
                    System.out.println("Field has been set");
                    break;
                default:
                    break;
            }
        }



    }

    private static void setValue(){
        while(true){
            try{
                value = thisSystem.ref("valueString", CommonClass.class, JConsistencyLevel.STRONG);
                System.out.println("Found Replicated Object");
                return;
            }catch (java.lang.IllegalArgumentException e){
                System.out.println("Not yet found");
            }
        }

    }

    static JReplicaSystem thisSystem;

    static JRef<@Strong CommonClass> value;

}
