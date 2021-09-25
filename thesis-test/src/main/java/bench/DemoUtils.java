package bench;

import java.util.List;

public class DemoUtils {
    public static void printResult(List<Double> values) {
        values.sort(Double::compare);
        double mean = values.stream().reduce(0., Double::sum) / values.size();
        double median = values.get(values.size()/2);
        double s = Math.sqrt(values.stream().map(x -> (x-mean)*(x-mean)).reduce(0., Double::sum) / (values.size()-1));
        double range = values.get(values.size()-1) - values.get(0);

        System.out.println("      mean:   " + mean);
        System.out.println("      median: " + median);
        System.out.println("      s:      " + s);
        System.out.println("      range:  " + range);
    }
}
