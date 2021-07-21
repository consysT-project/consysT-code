package com.readytalk.crdt.counters;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@RunWith(Suite.class)
@SuiteClasses({ GCounterTest.class, GCounterFactoryTest.class,
		PNCounterTest.class, PNCounterFactoryTest.class })
public class AllTests {

}
