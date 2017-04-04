package satsolving.blatt06.dataStructure;

public class TestCDCL {
	
	public static void main(String[] args) {
		ClauseSet cs;
		if(args.length == 1){
			cs = new ClauseSet(args[0]);
		}else{

			cs = new ClauseSet("src/satsolving/sat_instances/yes/aim-50-6_0-yes1-3.cnf");
		}
		
		System.out.println("begin the programm");
		CDCL cdcl = new CDCL(cs);
		System.out.println("Satisfiable? : " + cdcl.solve());
		System.out.println(cdcl);
		

	}
	
}
