package de.tuda.stg.consys.demo.messagegroups;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.demo.DemoRunnable;
import de.tuda.stg.consys.demo.DemoUtils;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.messagegroups.schema.Chat;
import de.tuda.stg.consys.demo.messagegroups.schema.Inbox;
import de.tuda.stg.consys.demo.messagegroups.schema.User;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.TransactionContext;
import de.tuda.stg.consys.logging.Logger;
import scala.Function1;
import scala.Option;

import java.util.*;
import java.util.concurrent.TimeoutException;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public class GroupChatBenchmark extends DemoRunnable {
    public static void main(String[] args) {
        JBenchExecution.execute("group-chat", GroupChatBenchmark.class, args);
    }



    public GroupChatBenchmark(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config);
    }

    @Override
    public void setup() {
    }

    @Override
    public void cleanup() {
    }

    @Override
    public void test() {
        if (processId() == 0) printTestResult();
    }

    @Override
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withUniformDistribution(new Runnable[0]);
    }


}
