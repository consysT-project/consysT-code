package de.tuda.stg.consys.invariants.lib;

import scala.Option;
import scala.Tuple2;
import scala.collection.immutable.HashMap;
import scala.collection.immutable.Map;
import scala.collection.mutable.ReusableBuilder;
import scala.jdk.javaapi.CollectionConverters;

import java.util.Iterator;
import java.util.function.Supplier;

public class Array<T> implements Iterable<T> {

    private final scala.collection.immutable.Map<Integer, T> elements;
    public final int length;
    private final Supplier<T> empty;

    private Array(Map<Integer, T> elements, int length, Supplier<T> empty) {
        this.elements = elements;
        this.length = length;
        this.empty = empty;
    }

    private Array(Map<Integer, T> elements, int length) {
        this(elements, length, () -> null);
    }

    public static <T> Array<T> from(T... elems) {
        ReusableBuilder<Tuple2<Integer, T>,HashMap<Integer,T>> builder = HashMap.<Integer, T>newBuilder();


        for (int i = 0; i < elems.length; i++)
            builder.addOne(new Tuple2<>(i, elems[i]));

        return new Array<>(builder.result(), elems.length);
    }

    public static <T> Array<T> emptyArray(int length) {
        return new Array(HashMap.<Integer, T>newBuilder().result(), length);
    }

    public static Array<Integer> emptyIntArray(int length) {
        return new Array(HashMap.<Integer, Integer>newBuilder().result(), length, () -> 0);
    }

    public Array<T> set(int index, T element) {
        if (index > length || index < 0)
            throw new ArrayIndexOutOfBoundsException("index was not in bounds: " + index + " (length: " + length + ")");

        return new Array<T>(elements.$plus(new Tuple2<>(index, element)), length);
    }

    public T get(int index) {
        if (index > length || index < 0)
            throw new ArrayIndexOutOfBoundsException("index was not in bounds: " + index + " (length: " + length + ")");

        Option<T> result = elements.get(index);

        if (result.isDefined()) {
            return result.get();
        }

        return empty.get();
    }


    @Override
    public Iterator<T> iterator() {
        return CollectionConverters.asJava(elements.valuesIterator());
    }
}
