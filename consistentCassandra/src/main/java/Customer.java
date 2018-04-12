import com.github.allprojects.consistencyTypes.qual.High;

public class Customer {

    @High static int id_count = 0;

    @High public String name;
    @High public int amount;
    @High public int id;

    @High public static int getNewID(){
        id_count++;
        return id_count;
    }

    @High public Customer(@High String n){
        this.id = Customer.getNewID();
        this.name = n;
        this.amount = 0;
    }
}
