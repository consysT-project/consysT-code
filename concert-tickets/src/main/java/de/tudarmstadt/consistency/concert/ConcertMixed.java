package de.tudarmstadt.consistency.concert;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.replobj.java.JRef;

import java.io.Serializable;
import java.util.Date;

public class ConcertMixed implements Serializable {
    public Date date;
    public JRef<@Strong ConcertHall> hall;
    public JRef<@Weak Band> band;
    public JRef<@Strong Counter> soldTickets;

    public @Strong int getSoldTickets () {
        return soldTickets.getField("value");
    }

    public Ticket buyTicket() {
        if (hall.<Integer>getField("maxAudience") > getSoldTickets()) {
            soldTickets.invoke("inc");
            return new Ticket();
        }
        else {
            return null;
        }
    }

    public ConcertMixed(Date date, JRef<@Strong ConcertHall> hall, JRef<@Weak Band> band, JRef<@Strong Counter> soldTickets) {
        this.date = date;
        this.hall = hall;
        this.band = band;
        this.soldTickets = soldTickets;
    }
}
