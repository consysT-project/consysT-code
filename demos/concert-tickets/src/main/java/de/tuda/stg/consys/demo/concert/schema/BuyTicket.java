package de.tuda.stg.consys.demo.concert.schema;

import de.tuda.stg.consys.objects.japi.JRef;

import java.io.Serializable;

/**
 * Created on 21.11.19.
 *
 * @author Mirko Köhler
 */
public class BuyTicket implements Serializable {
	private final JRef<ConcertHall> hall;
	private final JRef<Counter> soldTickets;

	public BuyTicket(JRef<ConcertHall> hall, JRef<Counter> soldTickets) {
		this.hall = hall;
		this.soldTickets = soldTickets;
	}

	public Ticket buyTicket() {
		if (hall.ref().maxAudience > soldTickets.ref().value) {
			soldTickets.ref().inc();
			return new Ticket();
		} else {
			return null;
		}
	}

}
