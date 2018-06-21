package de.tudarmstadt.consistency.checker;

import de.tudarmstadt.consistency.utils.Log;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.SuppressWarningsKeys;

@SuppressWarningsKeys({"consistency"})
public class ConsistencyChecker extends BaseTypeChecker {

    public ConsistencyChecker(){
        super();
        Log.info(ConsistencyChecker.class, "Running consistency checker...");
    }
}