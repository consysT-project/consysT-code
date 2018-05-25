package de.tu_darmstadt.consistency_types.example2;

import de.tu_darmstadt.consistency_types.checker.qual.Local;
import de.tu_darmstadt.consistency_types.checker.qual.Strong;
import de.tu_darmstadt.consistency_types.checker.qual.Weak;
import de.tu_darmstadt.consistency_types.store.Handle;

import java.util.UUID;

/**
 * Created on 18.05.18.
 *
 * @author Mirko Köhler
 */
public class Main {

	public static void main(String[] args) {

		try (CassandraDatabase database = CassandraDatabase.local()) {

			UUID id1 = new UUID(573489594L, 8675789563L);
			UUID id2 = new UUID(573489512L, 1675789528L);


			Handle<@Strong Integer> strong1 = database.obtain(id1, Strong.class);

			strong1.set(5);
			@Strong Integer dataA1 = strong1.get();


			Handle<@Strong Integer> strong2 = database.obtain(id1, Strong.class);

			strong2.set(7);
			@Strong Integer dataA2 = strong2.get();


			Handle<@Weak Integer> weak1 = database.obtain(id2, Weak.class);

			weak1.set(42);
			@Weak Integer dataB1 = weak1.get();

			//Types are correct: writing dataA2 (strong) to strong1 (strong)
			strong1.set(dataA2);

			//Types are correct: writing a local value to strong1 (strong)
			strong1.set(34);

			//Types are correct: writing dataA1 (strong) to weak1 (weak)
			weak1.set(dataA1);

			//Type clash: Assigning dataB1 (weak) to strong1 (strong)
			//strong1.set(dataB1);

			//Checking implicit flows
			if (weak1.get() == 32) {
				//strong1.set(11);
			}


		} catch (Exception e) {
			e.printStackTrace();
		}


	}
}
