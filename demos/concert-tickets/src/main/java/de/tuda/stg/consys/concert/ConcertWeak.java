package de.tuda.stg.consys.concert;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.japi.JRef;

import java.io.Serializable;
import java.util.Date;

public class ConcertWeak implements Serializable {
    public Date date;
    public JRef<@Weak ConcertHall> hall;
    public JRef<@Weak Band> band;
    public JRef<@Weak Counter> soldTickets;

    public @Weak int getSoldTickets () {
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

    public ConcertWeak(Date date, JRef<@Weak ConcertHall> hall, JRef<@Weak Band> band, JRef<@Weak Counter> soldTickets) {
        this.date = date;
        this.hall = hall;
        this.band = band;
        this.soldTickets = soldTickets;
    }
}
