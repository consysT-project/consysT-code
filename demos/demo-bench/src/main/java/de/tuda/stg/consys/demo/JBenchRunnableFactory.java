package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkRunnable;
import de.tuda.stg.consys.bench.BenchmarkRunnableFactory;
import de.tuda.stg.consys.core.store.extensions.DistributedStore;
import de.tuda.stg.consys.core.store.extensions.coordination.BarrierStore;
import de.tuda.stg.consys.japi.Store;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;

public class JBenchRunnableFactory {

    public static BenchmarkRunnableFactory fromClass(Class<? extends JBenchRunnable> clazz, JBenchStoreConverter storeConverter) {
        return new JBenchmarkClassRunnableFactory(clazz, storeConverter);
    }

    private static class JBenchmarkClassRunnableFactory implements BenchmarkRunnableFactory {
        private final Class<? extends JBenchRunnable> clazz;
        private final JBenchStoreConverter storeConverter;

        private JBenchmarkClassRunnableFactory(Class<? extends JBenchRunnable> clazz, JBenchStoreConverter storeConverter) {
            this.clazz = clazz;
            this.storeConverter = storeConverter;
        }

        //IDE Error due to Java/Scala interaction. This does compile.
        @Override
        public BenchmarkRunnable create(BarrierStore scalaStore, BenchmarkConfig config) {
            JBenchStore benchStore = storeConverter.convert(scalaStore);

            Constructor<? extends JBenchRunnable> benchConstructor;
            try {
                benchConstructor = clazz.getDeclaredConstructor(JBenchStore.class, BenchmarkConfig.class);

                var benchmark = benchConstructor.newInstance(benchStore, config);

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
