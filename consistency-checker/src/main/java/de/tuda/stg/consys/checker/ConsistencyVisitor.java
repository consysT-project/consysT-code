package de.tuda.stg.consys.checker;

import de.tuda.stg.consys.utils.Log;
import org.checkerframework.common.basetype.BaseTypeChecker;

public class ConsistencyVisitor extends ConsistencyVisitorImpl {

	public ConsistencyVisitor(BaseTypeChecker checker) {
        super(checker);
		Log.info(ConsistencyVisitor.class, "Initializing ConsistencyVisitor");
    }
}
