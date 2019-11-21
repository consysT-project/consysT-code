package de.tuda.stg.consys.demo.concert.schema;

import de.tuda.stg.consys.objects.japi.JRef;

import java.io.Serializable;
import java.util.Date;

public class Concert implements Serializable {
    private Date date;
    private final JRef<ConcertHall> hall;
    private final JRef<Band> band;
    private final JRef<Counter> soldTickets;
    private final JRef<BuyTicket> buyer;

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
