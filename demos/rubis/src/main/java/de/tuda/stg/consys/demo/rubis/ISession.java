package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.demo.rubis.schema.Category;
import de.tuda.stg.consys.demo.rubis.schema.IItem;
import de.tuda.stg.consys.demo.rubis.schema.IUser;
import de.tuda.stg.consys.demo.rubis.schema.ItemStatus;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.TransactionContext;
import scala.Option;

import java.util.Calendar;
import java.util.Date;

@SuppressWarnings({"consistency"})
public abstract class ISession {
    public static int nMaxRetries = 0;
    public static int retryDelay = 0;
    public static ConsistencyLevel<CassandraStore> userConsistencyLevel;
    public static ConsistencyLevel<CassandraStore> itemConsistencyLevel;

    protected float getInitialPrice(float reservePrice) {
        return reservePrice * 0.3f;
    }

    protected float getBuyNowPrice(float reservePrice) {
        return reservePrice * 1.3f;
    }

    protected Date getEndDateFromDuration(int durationInSeconds) {
        Calendar cal = Calendar.getInstance();
        cal.add(Calendar.SECOND, durationInSeconds);
        return cal.getTime();
    }

    public abstract String registerUser(TransactionContext tr, String userId, String nickname, String name, String password, String email);

    public abstract String registerItem(TransactionContext tr, String itemId, String name, String description,
                           Category category, float reservePrice, int durationInSeconds);

    public abstract void addBalance(TransactionContext tr, @Strong float amount);

    public abstract boolean placeBid(TransactionContext tr, String itemId, float bidAmount);

    public abstract void buyNow(TransactionContext tr, String itemId);

    public abstract void endAuctionImmediately(TransactionContext tr, String itemId);

    public abstract String browseItemsByItemIds(TransactionContext tr, String[] replIds);

    public abstract void rateUser(TransactionContext tr, String userId, int rating, String comment);

    public abstract float getBidPrice(TransactionContext tr, String itemId);

    public abstract ItemStatus getItemStatus(TransactionContext tr, String itemId);

    public abstract String getUser();
}
