package de.tuda.stg.consys.checker;

import de.tuda.stg.consys.utils.Log;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.SuppressWarningsKeys;

@SuppressWarningsKeys({"consistency"})
public class ConsistencyChecker extends BaseTypeChecker {

    public ConsistencyChecker(){
        super();
        Log.info(ConsistencyChecker.class, "Running consistency checker...");
    }
}