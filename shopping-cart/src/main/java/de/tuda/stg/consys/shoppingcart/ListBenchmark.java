package de.tuda.stg.consys.shoppingcart;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.jrefcollections.JRefLinkedList;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.Serializable;
import java.math.BigInteger;
import java.util.LinkedList;
import java.util.Random;

public class ListBenchmark implements Serializable {
    static Random rand = new Random();
    public static final double percentage = 0.1;
    public static final JRef<@Weak Item>[] pool = new JRef[5];

    public static void main(String... args) throws Exception {
        /*
        * To test:
        * Java Linked List as baseline,
        * JRefLinkedList (Weak and Strong)
        * JRefDistList with Strong nodes
        * JRefDistList with Weak nodes
        *
        * - Generate List With N entries
        * - randomly retrieve elements from list
        * - measure average access times
        * */

        JRef<@Weak Item> item1 = Replicas.replicaSystems[0].replicate("item1", new Item("item1", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item2 = Replicas.replicaSystems[0].replicate("item2", new Item("item2", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item3 = Replicas.replicaSystems[0].replicate("item3", new Item("item3", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item4 = Replicas.replicaSystems[0].replicate("item4", new Item("item4", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item5 = Replicas.replicaSystems[0].replicate("item5", new Item("item5", 15), JConsistencyLevel.WEAK);
        pool[0] = item1; pool[1] = item2;pool[2] = item3;pool[3] = item4;pool[4] = item5;

        int size = 100;

        System.out.println("Generating Random Order");
        int[] poolOrder = getRandomOrder(size);
        int[] accessOrder = getRandomAccess(size);



        System.out.println("Average Access for Linked List:" + BenchmarkLinkedList(poolOrder, accessOrder, size));

        System.out.println("Average Access for Weak JRef Linked List:" + BenchmarkJRefLinkedListWeak(poolOrder, accessOrder, size));

        System.out.println("Average Access for Strong JRef Linked List:" + BenchmarkJRefLinkedListStrong(poolOrder, accessOrder, size));

        //System.out.println("Average Access for Weak JRef Linked List:" + BenchmarkJRefLinkedListWeak(poolOrder, accessOrder, size));



        for (JReplicaSystem rep : Replicas.replicaSystems) {
            rep.close();
        }
    }

    private static double BenchmarkJRefLinkedListStrong(int[] poolOrder, int[] access, int size){
        double average = 0;
        BigInteger sum = new BigInteger("0");

        System.out.println("Generating JRef Linked List...");

        JRef<@Strong JRefLinkedList> jrefListStrong = Replicas.replicaSystems[0].replicate("jreflistStrong", new JRefLinkedList(), JConsistencyLevel.STRONG);
        for(int i=0;i < size ;i++){
            jrefListStrong.invoke("append", pool[poolOrder[i]]);
        }

        System.out.println("Starting Benchmark...");

        //Start benchmark
        for(int i=0;i < access.length ;i++){
            long start = System.nanoTime();
            jrefListStrong.invoke("get", access[i]);
            long end = System.nanoTime();
            sum = sum.add(BigInteger.valueOf((end-start)));
        }
        average = (sum.divide(BigInteger.valueOf(access.length))).longValue();

        //Somehow close jrefList again

        return average;
    }

    private static double BenchmarkJRefLinkedListWeak(int[] poolOrder, int[] access, int size){
        double average = 0;
        BigInteger sum = new BigInteger("0");

        System.out.println("Generating JRef Linked List...");

        JRef<@Weak JRefLinkedList> jrefListWeak = Replicas.replicaSystems[0].replicate("jreflistWeak", new JRefLinkedList(), JConsistencyLevel.WEAK);
        for(int i=0;i < size ;i++){
            jrefListWeak.invoke("append", pool[poolOrder[i]]);
        }

        System.out.println("Starting Benchmark...");

        //Start benchmark
        for(int i=0;i < access.length ;i++){
            long start = System.nanoTime();
            jrefListWeak.invoke("get", access[i]);
            long end = System.nanoTime();
            sum = sum.add(BigInteger.valueOf((end-start)));
        }
        average = (sum.divide(BigInteger.valueOf(access.length))).longValue();

        //Somehow close jrefList again

        return average;
    }

    private static double BenchmarkLinkedList(int[] poolOrder, int[] access, int size){
        double average = 0;
        BigInteger sum = new BigInteger("0");

        System.out.println("Generating Linked List...");

        LinkedList<JRef<@Weak Item>> javaLinkedList = new LinkedList<JRef<@Weak Item>>();
        for(int i=0;i < size ;i++){
            javaLinkedList.add(pool[poolOrder[i]]);
        }

        System.out.println("Starting Benchmark...");

        //Start benchmark
        for(int i=0;i < access.length ;i++){
            long start = System.nanoTime();
            javaLinkedList.get(access[i]);
            long end = System.nanoTime();
            sum = sum.add(BigInteger.valueOf((end-start)));
        }
        average = (sum.divide(BigInteger.valueOf(access.length))).longValue();

        return average;
    }

    //Returns an array with a random access order to access the list
    private static int[] getRandomAccess(int size){
        int[] ret = new int[(int) (size * percentage)];

        for (int i = 0; i < ret.length ;i++){
            ret[i] = rand.nextInt(size);
        }
        return ret;
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
