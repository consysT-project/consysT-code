public class Customer {

    static int id_count = 0;

    public String name;
    public int amount;
    public int id;

    public static int getNewID(){
        id_count++;
        return id_count;
    }

    public Customer(String n){
        this.id = Customer.getNewID();
        this.name = n;
        this.amount = 0;
    }
}
