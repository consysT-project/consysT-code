package de.tuda.stg.consys.casebenchmarkdist;

import java.io.*;
import java.nio.file.Paths;
import java.util.LinkedList;
import java.util.Random;

/**
 * A class for importing, exporting and generating content needed to fill the case study for the benchmark.
 */
public class ContentHandler{


    public static String[] searchableWords = {"Alfa", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot", "Golf",
            "Hotel", "India", "Juliett", "Kilo", "Lima", "Mike", "November", "Oscar", "Papa", "Quebec", "Romeo",
            "Sierra", "Tango", "Uniform", "Victor", "Whiskey", "Xray", "Yankee", "Zulu"};

    static public String[] readFile(String filename){
        String currLine = null;
        LinkedList<String> retList = new LinkedList<String>();

        try {
            FileReader fileReader =
                    new FileReader(filename);

            BufferedReader bufferedReader =
                    new BufferedReader(fileReader);

            while((currLine = bufferedReader.readLine()) != null) {
                retList.add(currLine);
            }

            bufferedReader.close();
        }
        catch(FileNotFoundException ex) {
            System.out.println(
                    "Unable to open file: '" +
                            filename + "'");
            System.out.println(
                    "Current Directory: '" +
                            Paths.get(".").toAbsolutePath().normalize().toString()
                    + "'"
            );
        }
        catch(IOException ex) {
            System.out.println(
                    "Error reading file '"
                            + filename + "'");
        }

        return retList.toArray(new String[retList.size()]);
    }

    static public boolean writeFile(String filename, String[] content){
        try {
            FileWriter fileWriter =
                    new FileWriter(filename);

            BufferedWriter bufferedWriter =
                    new BufferedWriter(fileWriter);

            for (String currLine: content) {
                bufferedWriter.write(currLine);
                bufferedWriter.newLine();
            }
            bufferedWriter.close();
            return true;
        }
        catch(IOException ex) {
            System.out.println(
                    "Error writing to file '"
                            + filename + "'");
            return false;
        }
    }

    static public String[] generateProducts(int count){
        Random r = new Random();
        String[] retArray = new String[count];
        for (int i = 0; i < count; i++){
            double price =  ((100 + r.nextInt(99900))/100);
            //Add one random searchable word to the products
            retArray[i] = new String("ProductName" + i + searchableWords[r.nextInt(searchableWords.length)] +
                    ";" + price);
        }
        return retArray;
    }

    static public String[] generateUsers(int count){
        Random r = new Random();
        String[] retArray = new String[count];
        for (int i = 0; i < count; i++){
            String pass = "";
            for(int j = 0; j < 6; j++){
                pass += (char) (r.nextInt(26) + 'a');
            }
            pass += r.nextInt(1000);
            retArray[i] = new String("User" + i + ";" + pass);
        }
        return retArray;
    }
}
