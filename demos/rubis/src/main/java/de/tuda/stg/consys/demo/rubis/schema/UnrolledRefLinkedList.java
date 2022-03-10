package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;
import java.util.UUID;
import java.util.function.Predicate;

// TODO: scrap this class, we need a B+ Tree
public class UnrolledRefLinkedList<E> implements Serializable {
    private final int MAX_ELEMENTS;
    private final ConsistencyLevel<CassandraStore> CONSISTENCY_LEVEL;
    private Ref<UnrolledRefLinkedList> next;
    private final ArrayList<E> elements;

    public UnrolledRefLinkedList(int maxElements, ConsistencyLevel<CassandraStore> consistencyLevel) {
        this.MAX_ELEMENTS = maxElements;
        this.elements = new ArrayList<>(maxElements);
        this.CONSISTENCY_LEVEL = consistencyLevel;
    }

    @Transactional
    public void add(E element, CassandraTransactionContextBinding tr) {
        if (elements.size() < MAX_ELEMENTS) {
            elements.add(element);
        } else if (next != null) {
            next.ref().add(element, tr);
        } else {
            this.next = tr.replicate(UUID.randomUUID().toString(), CONSISTENCY_LEVEL, UnrolledRefLinkedList.class,
                    MAX_ELEMENTS, CONSISTENCY_LEVEL);
        }
    }

    @Transactional
    public void remove(E element) {
        if (!elements.remove(element)) {
            next.ref().remove(element);
        }
        if (elements.isEmpty()) {
            this.next = (Ref<UnrolledRefLinkedList>) this.next.ref().next;
        }
    }

    @Transactional
    public void removeIf(Predicate<? super E> filter) {
        if (!elements.removeIf(filter)) {
            next.ref().removeIf(filter);
        }
    }

    @Transactional
    public List<E> get(int start, int end) {
        if (start > end)
            throw new IllegalArgumentException();

        if (end < MAX_ELEMENTS) {
            return elements.subList(start, end);
        } else if (start < MAX_ELEMENTS) {
            List<E> local = elements.subList(start, MAX_ELEMENTS);
            List<E> next = this.next.ref().get(0, end - MAX_ELEMENTS);
            List<E> merged = new ArrayList<>();
            merged.addAll(local);
            merged.addAll(next);
            return merged;
        } else {
            return this.next.ref().get(start - MAX_ELEMENTS, end);
        }
    }
}
