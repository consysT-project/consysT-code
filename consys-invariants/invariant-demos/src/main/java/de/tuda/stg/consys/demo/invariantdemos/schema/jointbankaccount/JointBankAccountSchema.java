//package de.tuda.stg.consys.demo.invariantdemos.schema.jointbankaccount;
//
//import de.tuda.stg.consys.demo.invariantdemos.Schema;
//import de.tuda.stg.consys.japi.legacy.JRef;
//
//import java.util.Random;
//
//public class JointBankAccountSchema extends Schema<JointBankAccount> {
//	Random random = new Random();
//
//	@Override
//	public JointBankAccount newInstance() {
//		return new JointBankAccount();
//	}
//
//	@Override
//	public Class<JointBankAccount> instanceClass() {
//		return JointBankAccount.class;
//	}
//
//	@Override
//	public void doOperation(JRef<JointBankAccount> ref) {
//		int rand = random.nextInt(100);
//		if (rand < 25) {
//			ref.invoke("deposit" , 100);
//		} else if (rand < 50) {
//			ref.invoke("withdraw" ,1);
//		} else if (rand < 75) {
//			ref.invoke("approve");
//		} else if (rand < 100) {
//			ref.invoke("request");
//		}
//	}
//}
