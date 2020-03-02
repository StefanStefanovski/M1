import java.io.*;
public class test {

   public static void main(String args[]) {
      String Str = new String("1,CA-2016-152156,11/8/16,11/11/16,Second Class,CG-12520,Claire Gute,Consumer,United States,Henderson,Kentucky,42420,South,FUR-BO-10001798,Furniture,Bookcases,Bush Somerset Collection Bookcase,261.96,2,0,41.9136,");

      System.out.println(Str.replace(',', ' '));


   }
}