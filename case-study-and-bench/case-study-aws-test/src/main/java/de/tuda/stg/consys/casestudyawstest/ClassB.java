package de.tuda.stg.consys.casestudyawstest;

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
        try{
            value = thisSystem.replicate("valueString", new CommonClass("from B"), JConsistencyLevel.STRONG);
            System.out.println("Successfully set value");
        }catch (IllegalArgumentException e){
            System.out.println("Value has already been set by another replica");
            value = thisSystem.ref("valueString", CommonClass.class, JConsistencyLevel.STRONG);
        }

    }

    static JReplicaSystem thisSystem;

    static JRef<@Strong CommonClass> value;

}
