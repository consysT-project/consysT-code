package de.tudarmstadt.consistency.store;

/**
 * Created on 21.06.18.
 *
 * @author Mirko Köhler
 */
public interface RefBuilder<R extends Ref<?, R>> {


	<T, RR extends R> RR build();
}
