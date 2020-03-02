
import java.io.IOException;
import java.time.Instant;
import java.util.Arrays;
import java.util.Hashtable;
import java.util.logging.FileHandler;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;

import org.apache.hadoop.conf.Configuration;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.io.DoubleWritable;
import org.apache.hadoop.io.IntWritable;
import org.apache.hadoop.io.LongWritable;
import org.apache.hadoop.io.Text;
import org.apache.hadoop.mapreduce.Job;
import org.apache.hadoop.mapreduce.Mapper;
import org.apache.hadoop.mapreduce.Reducer;
import org.apache.hadoop.mapreduce.lib.input.FileInputFormat;
import org.apache.hadoop.mapreduce.lib.input.TextInputFormat;
import org.apache.hadoop.mapreduce.lib.output.FileOutputFormat;
import org.apache.hadoop.mapreduce.lib.output.TextOutputFormat;

public class GroupBy {
	private static final String INPUT_PATH = "input-groupBy/";
	private static final String OUTPUT_PATH = "output/groupBy-";
	private static final Logger LOG = Logger.getLogger(GroupBy.class.getName());
	//private static final Hashtable <String, vg> attr =new Hashtable<String, Integer>();
	static {
		System.setProperty("java.util.logging.SimpleFormatter.format", "%5$s%n%6$s");

		try {
			FileHandler fh = new FileHandler("out.log");
			fh.setFormatter(new SimpleFormatter());
			LOG.addHandler(fh);
		} catch (SecurityException | IOException e) {
			System.exit(1);
		}
	}

	public static class Map extends Mapper<LongWritable, Text, Text, DoubleWritable> {

		@Override
		public void map(LongWritable key, Text value, Context context) {
			// TODO: à compléter

			
			String allLine = value.toString();
			String line = "Row ID,Order ID,Order Date,Ship Date,Ship Mode,Customer ID,Customer Name,Segment,Country,City,State,Postal Code,Region,Product ID,Category,Sub-Category,Product Name,Sales,Quantity,Discount,Profit,";
			String[] words = line.split(",");
			Integer index1 =0;
			//Integer index2 =0;
			Integer index3 =0;

			Integer i =0;
 			for(String word : words)
 				 
			{
				if(word.equals("Order ID"))
				{
					index1 = i;
				}
							
				if(word.equals("Quantity"))
				{
					index3 = i;
				}
				i++;		
			}
			
			String[] mots = allLine.split(",");
			//LOG.info(mots[index1]+"   "+ mots[index3]);
			
			//eviter les chaine de caracter
			try{
			int a = Integer.parseInt(mots[index3]);
			}
			catch(NumberFormatException e)
			{
				return; 
			}
			if ( mots[index3].equals("Quantity")){
				return;
			}
			

			double Quantity = Double.valueOf(mots[index3]);
			
			try {
				context.write(new Text(mots[index1]), new DoubleWritable(Quantity));
				
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			
			//ex4.1 & 4.2 : 
/*
 			for(String word : words)
 
			{
				if(word.equals("Ship Date"))
				{
					index1 = i;
				}
				
				if(word.equals("Category"))
				{
					index2 = i;
				}
				
				if(word.equals("Sales"))
				{
					index3 = i;
				}
				i++;		
			}
			
			String[] mots = allLine.split(",");
			LOG.info(mots[index1]+"   "+ mots[index2]+"   "+ mots[index3]);
			
			//eviter les chaine
			try{
			int a = Integer.parseInt(mots[index3]);
			}
			catch(NumberFormatException e)
			{
				return; 
			}
			if ( mots[index3].equals("Sales")){
				return;
			}
			
			double profit = Double.valueOf(mots[index3]);
			try {
				context.write(new Text(mots[index1]+"\t  "+mots[index2]+"\t  " ), new DoubleWritable(profit));
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			*/
			
			
			//Exo 3 : 
			/*
			for(String word : words)
			{
				if(word.equals("Customer ID"))
				{
					index1 = i;
				}
				
				if(word.equals("Profit"))
				{
					index2 = i;
				}
				i++;		
			}
			
			String[] mots = allLine.split(",");
			LOG.info(mots[index1]+"   "+ mots[index2]);
			
			if ( mots[index2].equals("Profit")){
				return;
			}
			double profit = Double.valueOf(mots[index2]);
			try {
				context.write(new Text(mots[index1]), new DoubleWritable(profit));
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			*/
		}
	}

	public static class Reduce extends Reducer<Text, DoubleWritable, Text, DoubleWritable> {

		@Override
		public void reduce(Text key, Iterable<DoubleWritable> values, Context context)
				throws IOException, InterruptedException {
			
			double sum = 0;
			Integer nbRep = 0; 
			
			for(DoubleWritable val : values)
			{
				sum += val.get();
				nbRep++;
			}
			
			context.write(new Text(key + "\t "+ nbRep), new DoubleWritable(sum));

		}
	}

	public static void main(String[] args) throws Exception {
		Configuration conf = new Configuration();

				
		Job job = new Job(conf, "GroupBy");

		job.setOutputKeyClass(Text.class);
		job.setOutputValueClass(Text.class);

		job.setMapperClass(Map.class);
		job.setReducerClass(Reduce.class);

		job.setOutputValueClass(DoubleWritable.class); 

		job.setInputFormatClass(TextInputFormat.class);
		job.setOutputFormatClass(TextOutputFormat.class);

		FileInputFormat.addInputPath(job, new Path(INPUT_PATH));
		FileOutputFormat.setOutputPath(job, new Path(OUTPUT_PATH + Instant.now().getEpochSecond()));

		job.waitForCompletion(true);
	}
}