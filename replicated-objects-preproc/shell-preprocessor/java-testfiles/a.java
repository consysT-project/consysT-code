

JRef<@Strong ObjA> ref1Strong = replicaSystem1.replicate("os", new ObjA(), ConsistencyLevels.Strong.class);


int i = ref1Strong.getField("f"); //.getField("f");

ref1Strong.setField("f", 42);

ref1Strong.invoke("inc");
ref1Strong.invoke("incBy", 4 + 21);

ref1Strong.invoke("incBy", 4 + (21 * 13) );