package de.tu_darmstadt.consistency_types.example2;

import de.tu_darmstadt.consistency_types.checker.qual.Strong;
import de.tu_darmstadt.consistency_types.checker.qual.Weak;
import de.tu_darmstadt.consistency_types.value.DatabaseValue;

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


			DatabaseValue<@Strong Integer> strong1 = database.strong().obtainValue(id1);

			strong1.write(5);
			Integer dataA1 = strong1.read();


			DatabaseValue<@Strong Integer> strong2 = database.strong().obtainValue(id1);

			strong2.write(7);
			Integer dataA2 = strong2.read();


			DatabaseValue<@Weak Integer> weak1 = database.weak().obtainValue(id2);

			weak1.write(42);
			Integer dataB1 = weak1.read();

			//Types are correct: writing dataA2 (strong) to strong1 (strong)
			strong1.write(dataA2);

			//Types are correct: writing a local value to strong1 (strong)
			strong1.write(34);

			//Types are correct: writing dataA1 (strong) to weak1 (weak)
			weak1.write(dataA1);

			//Type clash: Assigning dataB1 (weak) to strong1 (strong)
			//strong1.write(dataB1);

			//Checking implicit flows
			if (dataB1 == 42) {
				strong1.write(11);
			}


		} catch (Exception e) {
			e.printStackTrace();
		}


	}
}
