package satsolving.blatt06.dataStructure;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.Vector;

public class DimacsFormatReader {

	private BufferedReader br;
	private File file;
	private Vector<Vector<Integer>> context = new Vector<>();
	public DimacsFormatReader(String filename) {
		file = new File(filename);
	}

	public DimacsFormatReader(File file) {
		this.file = file;
	}

	public Vector< Vector<Integer> > read() {

		try {
			br = new BufferedReader(new FileReader(this.file));
			// get the file name

			String line;
			// read each line
			while ((line = br.readLine()) != null) {
				if (!line.startsWith("c") && !line.startsWith("p")) {
					String[] splits = line.trim().substring(0, line.length() - 2).split("\\s+");
					Vector<Integer> clause = new Vector<>();
					for(String s : splits){
						clause.add(Integer.parseInt(s));
					}
					context.add(clause);
				} else {
					continue;
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			this.close();
		}
		return this.context;
	}
	

	public void close() {
		try {
			if (br != null)
				br.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public static void main(String[] args) {
		DimacsFormatReader dr = new DimacsFormatReader("src/satsolving/sat_instances/formula01.cnf");
		
		System.out.println(dr.read().toString());
		dr.close();
	}

	

}
