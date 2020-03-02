import java.io.IOException;
import java.time.Instant;
import java.util.ArrayList;
import java.util.logging.FileHandler;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;

import org.apache.hadoop.conf.Configuration;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.io.LongWritable;
import org.apache.hadoop.io.Text;
import org.apache.hadoop.mapreduce.Job;
import org.apache.hadoop.mapreduce.Mapper;
import org.apache.hadoop.mapreduce.Reducer;
import org.apache.hadoop.mapreduce.lib.input.FileInputFormat;
import org.apache.hadoop.mapreduce.lib.input.TextInputFormat;
import org.apache.hadoop.mapreduce.lib.output.FileOutputFormat;
import org.apache.hadoop.mapreduce.lib.output.TextOutputFormat;

public class Join {
	private static final String INPUT_PATH = "input-join-compact/";
	private static final String OUTPUT_PATH = "output/join-";
	private static final Logger LOG = Logger.getLogger(Join.class.getName());
		
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
	
	public static class Map extends Mapper<LongWritable, Text, Text, Text> {

		public void map(LongWritable key, Text value, Context context) throws IOException, InterruptedException {
			String line = value.toString();
			String[] words = line.split("\\|");
			
			if (words.length == 9) 
				context.write(new Text(words[1]), new Text("orders|" + words[8]));
			else 
				context.write(new Text(words[0]), new Text("customers|" + words[1]));
		}		
	}

	public static class Reduce extends Reducer<Text, Text, Text, Text> {

		public void reduce(Text key, Iterable<Text> values, Context context) throws IOException, InterruptedException {
			ArrayList<Text> tmp = new ArrayList<>();
			
			for (Text val : values)
				tmp.add(new Text(val));
			
			for (Text a : tmp) {
				for (Text b : tmp) {
					String as[] = a.toString().split("\\|");
					String bs[] = b.toString().split("\\|");
					if (as[0].equals("orders") && bs[0].equals("customers"))
						context.write(key, new Text(as[1] + " : " + bs[1]));
				}
			}				
		}
	}

	public static void main(String[] args) throws Exception {
		Configuration conf = new Configuration();
				
		Job job = new Job(conf, "Join");

		job.setOutputKeyClass(Text.class);
		job.setOutputValueClass(Text.class);

		job.setMapperClass(Map.class);
		job.setReducerClass(Reduce.class);

		job.setInputFormatClass(TextInputFormat.class);
		job.setOutputFormatClass(TextOutputFormat.class);

		FileInputFormat.addInputPath(job, new Path(INPUT_PATH));
		FileOutputFormat.setOutputPath(job, new Path(OUTPUT_PATH + Instant.now().getEpochSecond()));

		job.waitForCompletion(true);
	}

}
