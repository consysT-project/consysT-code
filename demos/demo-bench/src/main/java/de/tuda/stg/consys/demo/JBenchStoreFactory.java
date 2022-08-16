package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.bench.StoreBenchmarkConfig;
import de.tuda.stg.consys.core.store.Store;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;

public interface JBenchStoreFactory<ScalaStore extends Store, JavaStore extends de.tuda.stg.consys.japi.Store> {
    JBenchStore<JavaStore> create(ScalaStore store);





}
