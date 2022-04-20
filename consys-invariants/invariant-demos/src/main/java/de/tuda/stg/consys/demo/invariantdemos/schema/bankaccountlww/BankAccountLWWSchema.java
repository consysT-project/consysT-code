//package de.tuda.stg.consys.demo.invariantdemos.schema.bankaccountlww;
//
//import de.tuda.stg.consys.demo.invariantdemos.Schema;
//import de.tuda.stg.consys.japi.legacy.JRef;
//
//import java.util.Random;
//
//public class BankAccountLWWSchema extends Schema<BankAccountLWW> {
//	Random random = new Random();
//
//	@Override
//	public BankAccountLWW newInstance() {
//		return new BankAccountLWW();
//	}
//
//	@Override
//	public Class<BankAccountLWW> instanceClass() {
//		return BankAccountLWW.class;
//	}
//
//	@Override
//	public void doOperation(JRef<BankAccountLWW> ref) {
//		int rand = random.nextInt(100);
//		if (rand < 50) {
//			ref.invoke("deposit", 100);
//		} else if (rand < 100) {
//			ref.invoke("withdraw" , 1);
//		}
//	}
//}
