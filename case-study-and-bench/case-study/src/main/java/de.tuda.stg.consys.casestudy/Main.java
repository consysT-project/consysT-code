package de.tuda.stg.consys.casestudy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.Serializable;
import java.util.LinkedList;

public class Main implements Serializable {

    public static void main(String... args) throws Exception {

    }

    JReplicaSystem[] replicaSystems;

    JRef<@Strong Database> database;

    LinkedList<JRef<@Weak ShoppingSite>> sites;

    private void setUpReplicaSystems(int systemCount){
        replicaSystems = new JReplicaSystem[systemCount];

        for (int i = 0; i < systemCount; i++) {
            replicaSystems[i] = JReplicaSystem.fromActorSystem(2552 + i);
        }

        for (int i = 0; i < systemCount; i++) {
            for (int j = 0; j < systemCount; j++) {
                if (i != j)
                    replicaSystems[i].addReplicaSystem("127.0.0.1", 2552 + j);
            }
        }
    }

    private boolean setUpDatabase(int repSysNum){
        if(repSysNum < 0 || repSysNum >= replicaSystems.length){
            return false;
        }else {
            database = replicaSystems[repSysNum].replicate("database",
                    new Database(), JConsistencyLevel.STRONG);
            database.invoke("init");
            return true;
        }
    }

    private boolean setUpSites(){
        sites = new LinkedList<JRef<@Weak ShoppingSite>>();
        for (JReplicaSystem sys: replicaSystems) {
            sites.add(sys.replicate(new ShoppingSite(database), JConsistencyLevel.WEAK));
        }
        return true;
    }
}
