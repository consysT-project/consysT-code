package de.tuda.stg.consys.invariants.lib.crdts;

public class CRDTTest {

	public static void main(String[] args) {
		BoundedCounter c0 = new BoundedCounter(0);
		BoundedCounter c1 = new BoundedCounter(1);

		c0.increment(30);
		c1.increment(5);

		assert c0.getValue() == 30;
		assert c1.getValue() == 5;
		assert c0.getQuota() == 30;
		assert c1.getQuota() == 5;

		c0.merge(c1);
		c1.merge(c0);

		assert c0.getValue() == 35;
		assert c1.getValue() == 35;
		assert c0.getQuota() == 30;
		assert c1.getQuota() == 5;

		c0.transfer(1, 20);
		c0.decrement(8);

		assert c0.getValue() == 27;
		assert c1.getValue() == 35;
		assert c0.getQuota() == 2;
		assert c1.getQuota() == 5;

		c0.merge(c1);
		c1.merge(c0);

		assert c0.getValue() == 27;
		assert c1.getValue() == 27;
		assert c0.getQuota() == 2;
		assert c1.getQuota() == 25;

		c0.increment(13);
		c1.decrement(20);

		assert c0.getValue() == 40;
		assert c1.getValue() == 7;
		assert c0.getQuota() == 15;
		assert c1.getQuota() == 5;

		c0.merge(c1);
		c1.merge(c0);

		assert c0.getValue() == 20;
		assert c1.getValue() == 20;
		assert c0.getQuota() == 15;
		assert c1.getQuota() == 5;

		c1.transfer(0, 5);

		assert c0.getValue() == 20;
		assert c1.getValue() == 20;
		assert c0.getQuota() == 15;
		assert c1.getQuota() == 0;

		c0.merge(c1);
		c1.merge(c0);

		assert c0.getValue() == 20;
		assert c1.getValue() == 20;
		assert c0.getQuota() == 20;
		assert c1.getQuota() == 0;

		c0.decrement(20);

		c0.merge(c1);
		c1.merge(c0);

		assert c0.getValue() == 0;
		assert c1.getValue() == 0;
		assert c0.getQuota() == 0;
		assert c1.getQuota() == 0;

		System.out.println("done");
	}

}
