package de.tuda.stg.consys.demo.concert.schema;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.japi.JRef;

import java.io.Serializable;
import java.util.Date;

public class Concert implements Serializable {
    public Date date;
    public JRef<ConcertHall> hall;
    public JRef<Band> band;
    public JRef<Counter> soldTickets;

    public int getSoldTickets () {
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

    public Concert(Date date, JRef<ConcertHall> hall, JRef<Band> band, JRef<Counter> soldTickets) {
        this.date = date;
        this.hall = hall;
        this.band = band;
        this.soldTickets = soldTickets;
    }
}
