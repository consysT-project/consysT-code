//package de.tuda.stg.consys.demo.invariantdemos.schema.consensus;
//
//import de.tuda.stg.consys.demo.invariantdemos.Schema;
//import de.tuda.stg.consys.japi.legacy.JRef;
//import de.tuda.stg.consys.invariants.lib.InvariantUtils;
//
//import java.util.Random;
//
//public class ConsensusSchema extends Schema<Consensus> {
//	@Override
//	public Consensus newInstance() {
//		return new Consensus(InvariantUtils.replicaId());
//	}
//
//	@Override
//	public Class<Consensus> instanceClass() {
//		return Consensus.class;
//	}
//
//	private final Random random = new Random();
//
//	@Override
//	public void doOperation(JRef<Consensus> ref) {
//		int rand = random.nextInt(100);
//		if (rand < 50) {
//			ref.invoke("agree");
//		} else if (rand < 100) {
//			ref.invoke("mark");
//		}
//	}
//}
