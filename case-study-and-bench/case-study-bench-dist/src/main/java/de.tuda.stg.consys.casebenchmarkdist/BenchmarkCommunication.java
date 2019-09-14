package de.tuda.stg.consys.casebenchmarkdist;

import java.io.Serializable;

/**
 * A class for figuring out everything related to connecting replica systems
 * and figuring out which one is supposed to do what when.
 */
public class BenchmarkCommunication implements Serializable {
    //A boolean indicating if the benchmark finished running, is set on benchmark teardown
    public boolean finishedRunning;
    //An array used for each replica system to indicate if they are finished setting up
    public boolean[] statusReport;
    //A boolean indicating if the system responsible for setup finished setup
    public boolean setupInstanceReady;
    //A boolean indicating that the system responsible for running is requesting a setup from the setup instance
    public boolean requestInstanceSetup;
    //A boolean indiciating that the system responsible for running is requesting the database to be deleted from the setup instance
    public boolean requestDBteardown;
    //The login users to be set by the server instance and read by the benchmark instance
    // to be set on when also setting other components
    public String[] loginUsers;
    //The location of the benchamark instance (host;port)
    public String benchmarkInstanceLocation;
    //Whether the benchmark Instance is online
    public boolean benchmarkInstanceOnline;

    //The number of replica systems involved
    private int total;

    public String msg;

    public BenchmarkCommunication(int totalCount){
        statusReport = new boolean[totalCount];
        //finishedRunning = true;
        total = totalCount;
        setupInstanceReady = false;
        requestInstanceSetup = false;
    }

    public void setReady(int orderInfo){
        statusReport[orderInfo - 1] = true;
        System.out.println("System " + orderInfo + " is ready!");
    }

    //A function that returns if all replica systems are ready
    public boolean confirmReady(){
        for (boolean val:statusReport) {
            System.out.println(val);
            if(!val)
                return val;
        }
        return true;
    }
}