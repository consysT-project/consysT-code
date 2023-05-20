package de.tuda.stg.consys.demo.docshare;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.demo.DemoRunnable;
import de.tuda.stg.consys.demo.DemoUtils;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.docshare.schema.opcentric.Document;
import de.tuda.stg.consys.demo.docshare.schema.opcentric.User;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.logging.Logger;
import scala.Option;

import java.util.ArrayList;
import java.util.List;

@SuppressWarnings({"consistency"})
public class DocShareBenchmark extends DemoRunnable {
    public static void main(String[] args) {
        JBenchExecution.execute("doc-share", DocShareBenchmark.class, args);
    }

    private int numOfUsersPerReplica;
    private final List<Session> localSessions;
    private final List<Ref<? extends User>> users;
    private final List<Ref<? extends Document>> documents;


    public DocShareBenchmark(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config);

        localSessions = new ArrayList<>();
        users = new ArrayList<>();
        documents = new ArrayList<>();

        numOfUsersPerReplica = config.toConfig().getInt("consys.bench.demo.docshare.users");

        Session.userConsistencyLevel = getLevelWithMixedFallback(getMixedLevel());
        Session.documentConsistencyLevel = getLevelWithMixedFallback(getMixedLevel());
    }


    @Override
    public void setup() {
        Logger.debug(procName(), "Creating objects");

        for (int userIndex = 0; userIndex < numOfUsersPerReplica; userIndex++) {
            var session = new Session((CassandraStoreBinding) store());
            localSessions.add(session);

            session.initUser(DemoUtils.addr("user", userIndex, processId()));
            session.addDocument(DemoUtils.addr("document", userIndex, processId()), DemoUtils.generateRandomText(1));

            BenchmarkUtils.printProgress(userIndex);
        }

        barrier("users_added");

        Logger.debug(procName(), "Collecting objects");

        for (int userIndex = 0; userIndex < numOfUsersPerReplica; userIndex++) {
            for (int replicaIndex = 0; replicaIndex < nReplicas; replicaIndex++) {
                users.add(localSessions.get(0).findUser(DemoUtils.addr("user", userIndex, replicaIndex)));
                documents.add(localSessions.get(0).findDocument(DemoUtils.addr("document", userIndex, replicaIndex)));
            }
        }


        BenchmarkUtils.printDone();
    }

    @Override
    public void cleanup() {
        localSessions.clear();
        users.clear();
        documents.clear();
    }

    @Override
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withZipfDistribution(new Runnable[] {
                this::addDocument,
                this::editDocumentContent,
                this::editDocumentDescription,
                this::readDocument,
        });
    }

    private void addDocument() {
        Session session = DemoUtils.getRandomElement(localSessions);
        session.addDocument(DemoUtils.generateRandomText(1));
    }


    private void editDocumentContent() {
        Session session = DemoUtils.getRandomElement(localSessions);

        store().transaction(ctx ->
        {
            var document = (Ref<Document>) DemoUtils.getRandomElement(documents);

            try {
                session.editDocumentContent(document, DemoUtils.generateRandomText(30));
                return Option.apply(0);
            } catch (IllegalArgumentException e) {
                System.err.println("Exception raised by app: " + e.getMessage());
                return Option.apply(e);
            }
        });
    }

    private void editDocumentDescription() {
        Session session = DemoUtils.getRandomElement(localSessions);

        store().transaction(ctx ->
        {
            var document = (Ref<Document>) DemoUtils.getRandomElement(documents);

            try {
                session.editDocumentDescription(document, DemoUtils.generateRandomText(3));
                return Option.apply(0);
            } catch (IllegalArgumentException e) {
                System.err.println("Exception raised by app: " + e.getMessage());
                return Option.apply(e);
            }
        });
    }

    private void readDocument() {
        Session session = DemoUtils.getRandomElement(localSessions);

        int userIndex = random.nextInt(numOfUsersPerReplica);
        int replicaIndex = random.nextInt(nReplicas);

        session.findDocument(DemoUtils.addr("document", userIndex, replicaIndex));
    }

}
