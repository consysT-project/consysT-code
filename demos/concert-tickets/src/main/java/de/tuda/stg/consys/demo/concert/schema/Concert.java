package de.tuda.stg.consys.demo.concert.schema;

import de.tuda.stg.consys.japi.legacy.JRef;

import java.io.Serializable;
import java.util.Date;

public class Concert implements Serializable {
    private Date date;
    public final JRef<ConcertHall> hall;
    public final JRef<Band> band;
    public final JRef<Counter> soldTickets;
    public final JRef<BuyTicket> buyer;

    public int getSoldTickets () {
        return soldTickets.ref().value;
    }

    public String getBandName() {
        return band.ref().name;
    }

    public Date getDate() {
        return date;
    }

    public Ticket buyTicket() {
        return buyer.ref().buyTicket();
    }


    public Concert(Date date, JRef<ConcertHall> hall, JRef<Band> band, JRef<Counter> soldTickets, JRef<BuyTicket> buyer) {
        this.date = date;
        this.hall = hall;
        this.band = band;
        this.soldTickets = soldTickets;
        this.buyer = buyer;
    }
}
