package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.japi.Store;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;

public abstract class JBenchOperationFactory<StoreType extends Store> {

    public abstract JBenchRunnable<StoreType> create(JBenchStore<StoreType> store, BenchmarkConfig config);


    public static JBenchOperationFactory fromClass(Class<? extends JBenchRunnable> clazz) {
        return new JStoreBenchmarkOpsClassFactory(clazz);
    }


    private static class JStoreBenchmarkOpsClassFactory extends JBenchOperationFactory {
        private final Class<? extends JBenchRunnable> clazz;

        private JStoreBenchmarkOpsClassFactory(Class<? extends JBenchRunnable> clazz) {
            this.clazz = clazz;
        }

        @Override
        public JBenchRunnable create(JBenchStore store, BenchmarkConfig config) {

            Constructor<? extends JBenchRunnable> benchConstructor;
            try {
                benchConstructor = clazz.getDeclaredConstructor(JBenchStore.class, BenchmarkConfig.class);

                var benchmark = benchConstructor.newInstance(store, config);
                return benchmark;

            } catch (NoSuchMethodException e) {
                System.err.println("Failed to initialize benchmark. Constructor not found: " + e.getMessage());
                throw new IllegalArgumentException(e);
            } catch (InstantiationException e) {
                throw new RuntimeException(e);
            } catch (IllegalAccessException e) {
                throw new RuntimeException(e);
            } catch (InvocationTargetException e) {
                throw new RuntimeException(e);
            }

        }
    }

}
