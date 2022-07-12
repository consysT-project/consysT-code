package de.tuda.stg.consys.checker.jdk;

import com.sun.source.util.JavacTask;
import com.sun.tools.javac.api.BasicJavacTask;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import de.tuda.stg.consys.annotations.MixedField;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.TypeAnnotationUtils;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationValue;
import javax.lang.model.element.Element;
import java.util.Map;

public class Utils {
    public static void storeDeclarationAnnotation(Element elt, Map<String, AnnotationValue> values, AnnotatedTypeFactory tf) {
        var sym = (Symbol) elt;
        for (var a : sym.getDeclarationAttributes()) {
            // only add if not already present
            if (a.getAnnotationType().asElement().getSimpleName().toString().equals("MixedField")) {
                return;
            }
        }

        var annotation = AnnotationBuilder.fromClass(tf.getElementUtils(), MixedField.class, values);
        sym.appendAttributes(List.of(
                TypeAnnotationUtils.createCompoundFromAnnotationMirror(annotation, tf.getProcessingEnv())));
    }

    public static void log(String msg, ProcessingEnvironment env) {
        // TODO: does not log if same message was already logged before
        Log.instance(((BasicJavacTask) JavacTask.instance(env)).getContext()).printRawLines(Log.WriterKind.STDOUT, msg);
    }
}
