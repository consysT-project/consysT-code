package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.bench.StoreBenchmarkConfig;
import de.tuda.stg.consys.japi.Store;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;

public abstract class JBenchOperationFactory<StoreType extends Store> {

    public abstract JBenchOperation<StoreType> create(JBenchStore<StoreType> store, StoreBenchmarkConfig config);


    public static JBenchOperationFactory fromClass(Class<? extends JBenchOperation> clazz) {
        return new JStoreBenchmarkOpsClassFactory(clazz);
    }


    private static class JStoreBenchmarkOpsClassFactory extends JBenchOperationFactory {
        private final Class<? extends JBenchOperation> clazz;

        private JStoreBenchmarkOpsClassFactory(Class<? extends JBenchOperation> clazz) {
            this.clazz = clazz;
        }

        @Override
        public JBenchOperation create(JBenchStore store, StoreBenchmarkConfig config) {

            Constructor<? extends JBenchOperation> benchConstructor;
            try {
                benchConstructor = clazz.getDeclaredConstructor(JBenchStore.class, StoreBenchmarkConfig.class);

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
