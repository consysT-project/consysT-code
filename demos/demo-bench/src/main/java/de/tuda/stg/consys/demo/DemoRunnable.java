package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.TransactionContext;

import java.util.*;

public abstract class DemoRunnable<
        Addr,
        Obj,
        TxContext extends TransactionContext<Addr, Obj, ConsistencyLevel<SStore>>,
        JStore extends Store<Addr, Obj, ConsistencyLevel<SStore>, TxContext>,
        SStore extends de.tuda.stg.consys.core.store.Store
        > extends JBenchRunnable<Addr, Obj, TxContext, JStore, SStore> {
    protected enum BenchmarkType {
        WEAK, MIXED, STRONG, OP_MIXED, WEAK_DATACENTRIC, STRONG_DATACENTRIC, DATACENTRIC_MIXED_IN_OPCENTRIC_IMPL
    }

    protected final BenchmarkType benchType;

    protected final int nReplicas;

    protected boolean isTestMode = false;

    // utility for benchmarks
    protected final Random random = new Random();

    public DemoRunnable(JBenchStore<Addr, Obj, TxContext, JStore, SStore> adapter, BenchmarkConfig config) {
        super(adapter, config);

        String typeString = config.toConfig().getString("consys.bench.demo.type");
        if (typeString == null) {
            throw new IllegalArgumentException("config key not found: consys.bench.demo.type");
        }

        benchType = BenchmarkType.valueOf(typeString.toUpperCase());
        nReplicas = config.numberOfReplicas();
    }

    @Override
    public void enableTests() {
        isTestMode = true;
    }

    protected String procName() {
        return "proc-" + processId();
    }

    protected ConsistencyLevel<SStore> getLevelWithMixedFallback(ConsistencyLevel<SStore> mixedLevel) {
        switch (benchType) {
            case WEAK:
            case WEAK_DATACENTRIC: return getWeakLevel();
            case STRONG:
            case STRONG_DATACENTRIC: return getStrongLevel();
            case OP_MIXED: return getMixedLevel();
            case DATACENTRIC_MIXED_IN_OPCENTRIC_IMPL:
            case MIXED: return mixedLevel;
            default: throw new UnsupportedOperationException("unknown bench type");
        }
    }

    public void check(String name, boolean result) {
        TestCollector.check(name, result);
    }

    public void printTestResult() {
        TestCollector.printTestResult();
    }
}
