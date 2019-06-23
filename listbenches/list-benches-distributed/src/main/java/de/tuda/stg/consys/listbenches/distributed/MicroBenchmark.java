package de.tuda.stg.consys.listbenches.distributed;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.jrefcollections.JRefDistList;
import de.tuda.stg.consys.objects.ConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import de.tuda.stg.consys.shoppingcart.Item;
import org.openjdk.jmh.Main;
import org.openjdk.jmh.annotations.*;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.Random;
import java.util.concurrent.TimeUnit;


@Warmup(iterations = 5)
@Measurement(iterations = 10)
@BenchmarkMode(Mode.SampleTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@Fork(5)
public class MicroBenchmark {

    public static void main(String[] args) throws Exception {
        Main.main(args);
    }


    @State(Scope.Benchmark)
    public static class BenchmarkSetup{
        @Param({"weak", "strong"})
        String level;

        //The number of elements in percent that is changed between every access
        @Param({"5","10","15"})
        String changeBeforeGet;

        //The size of the list
        @Param({"100","500","1000","1500","2000","2500"})
        String sizeParam;

        static Random rand = new Random();
        public static double percentage;

        int size;

        int index;

        int[] itemOrder;

        JReplicaSystem replicaSystem1;
        JReplicaSystem replicaSystem2;
        JReplicaSystem replicaSystem3;

        JRef<JRefDistList> list;

        JRef<JRefDistList> listref1;
        JRef<JRefDistList> listref2;

        public static final JRef<@Weak Item>[] pool = new JRef[5];

        @Setup(Level.Iteration)
        public void systemSetup() throws Exception {
            switch(sizeParam){
                case "100": size = 100; break;
                case "500": size = 500; break;
                case "1000": size = 1000; break;
                case "1500": size = 1500; break;
                case "2000": size = 2000; break;
                case "2500": size = 2500; break;
                case "10000": size = 10000; break;
            }

            switch(changeBeforeGet){
                case "0": percentage = 0; break;
                case "5": percentage = 0.05; break;
                case "10": percentage = 0.10; break;
                case "15": percentage = 0.15; break;
            }

            replicaSystem1 = JReplicaSystem.fromActorSystem(2552);
            replicaSystem2 = JReplicaSystem.fromActorSystem(2553);
            replicaSystem3 = JReplicaSystem.fromActorSystem(2554);

            replicaSystem1.addReplicaSystem("127.0.0.1", 2553);
            replicaSystem1.addReplicaSystem("127.0.0.1", 2554);
            replicaSystem2.addReplicaSystem("127.0.0.1", 2552);
            replicaSystem2.addReplicaSystem("127.0.0.1", 2554);
            replicaSystem3.addReplicaSystem("127.0.0.1", 2552);
            replicaSystem3.addReplicaSystem("127.0.0.1", 2553);

            ConsistencyLevel consistencyLevel = level.equals("weak") ? JConsistencyLevel.WEAK : JConsistencyLevel.STRONG;

            list = replicaSystem1.replicate("list", new JRefDistList(consistencyLevel), consistencyLevel);

            listref1 = replicaSystem2.ref("list", JRefDistList.class, consistencyLevel);
            listref2 = replicaSystem3.ref("list", JRefDistList.class, consistencyLevel);

            JRef<@Weak Item> item1 = replicaSystem1.replicate("item1", new Item("item1", 15), JConsistencyLevel.WEAK);
            JRef<@Weak Item> item2 = replicaSystem1.replicate("item2", new Item("item2", 20), JConsistencyLevel.WEAK);
            JRef<@Weak Item> item3 = replicaSystem1.replicate("item3", new Item("item3", 30), JConsistencyLevel.WEAK);
            JRef<@Weak Item> item4 = replicaSystem1.replicate("item4", new Item("item4", 40), JConsistencyLevel.WEAK);
            JRef<@Weak Item> item5 = replicaSystem1.replicate("item5", new Item("item5", 50), JConsistencyLevel.WEAK);

            pool[0] = item1; pool[1] = item2;pool[2] = item3;pool[3] = item4;pool[4] = item5;

            itemOrder = getRandomOrder(size);

            for(int i=0;i < size ;i++){
                list.invoke("append", pool[itemOrder[i]], replicaSystem1);
            }

            listref1.sync();
            listref2.sync();

            Thread.sleep(1000);
        }

        @Setup(Level.Invocation)
        public void systemStep() throws Exception {
            index = rand.nextInt(size);

            if(percentage > 0){
                int numOfElems = (int) (percentage * size);
                for(int i = 0; i<numOfElems ;i++){
                    int changepos = rand.nextInt(size);
                    //Remove and readd the element.
                    JRef ref = list.invoke("removeIndex", changepos);
                    list.invoke("append", ref, replicaSystem1);
                }
            }
        }


        @TearDown(Level.Iteration)
        public void systemTeardown() throws Exception {
            replicaSystem1.close();
            replicaSystem2.close();
            replicaSystem3.close();
        }

        //Returns an array with a random order of items to put into the list
        private static int[] getRandomOrder(int size){
            int[] ret = new int[size];

            for (int i = 0; i < ret.length ;i++){
                ret[i] = rand.nextInt(pool.length);
            }
            return ret;
        }
    }

    @Benchmark
    public JRef<@Weak Item> benchmarkGet(BenchmarkSetup setup) {
        JRef<@Weak Item> ret = setup.listref1.invoke("getIndex", setup.index);
        return ret;
    }
}
