package satsolving.blatt06.dataStructure;

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Optional;
import java.util.Stack;
import java.util.Vector;
import java.util.stream.Collectors;

import satsolving.blatt06.dataStructure.Clause.ClauseState;
import satsolving.blatt06.dataStructure.Variable.State;

/**
 * A set of clauses.
 * 
 */
public class ClauseSet {
	/* Number of variables */
	private int varNum;

	/* Clauses of this set */
	private Vector<Clause> clauses;

	/* List of all variables */
	private HashMap<Integer, Variable> variables;

	/* actual unit clauses */
	private Vector<Clause> units;

	/**
	 * Constructs a clause set from the given DIMACS file.
	 * 
	 * @param filePath
	 *            file path of the DIMACS file.
	 */
	public ClauseSet(String filePath) {
		DimacsFormatReader reader = new DimacsFormatReader(filePath);
		// the context of the .cnf file. Type of the context is
		// Vector<Vector<Integer>>
		Vector<Vector<Integer>> context = reader.read();
		this.variables = new HashMap<>();
		this.clauses = new Vector<>();
		// for(Vector<Integer> clause : context){
		// clauses.add(new Clause(clause,variables));
		// }
		context.forEach(clause -> this.clauses.add(new Clause(clause, this.variables)));
		this.varNum = variables.size();
		this.units = new Vector<>();
	}

	/**
	 * 
	 * @return empty clause if found, otherwise null
	 */
	public Clause unitPropagation(int level, Stack<Variable> stack) {
		// obtain init unitclause by observing the return value of
		// Clause.initWatch (return type is ClauseState)
		// then from now on, don't need to search the next unit clause. But
		// assign method

		Clause emptyClause = null;
		for (Clause clause : clauses) {
			if (clause.getState() == ClauseState.UNIT) {
				units.add(clause);
			}
		}

		Integer literal; // the unassigned literal
		Vector<Clause> clone = (Vector<Clause>) units.clone();
		Iterator<Clause> iter = clone.iterator();
		// to avoid exception, set up a help vector to save the unit clause that
		// has been iterated
		Vector<Clause> iteratedUnitClause = new Vector<>();

		while (iter.hasNext()) {
			Clause currentUnitClause = iter.next();
			iteratedUnitClause.add(currentUnitClause);
			literal = currentUnitClause.getUnassigned(variables);
			if (literal > 0) {
				emptyClause = variables.get(Math.abs(literal)).assign(true, this.variables, units, level, stack);
			} else if (literal < 0) {
				emptyClause = variables.get(Math.abs(literal)).assign(false, this.variables, units, level, stack);
			} else {
				System.err.println("found the literal 0");
			}

			if (emptyClause != null) {
				break;
			}
			/*
			 * get clone of units, remove clauses which are already iterated.
			 * reassign the iterator.
			 */
			if (!iter.hasNext()) {
				clone = (Vector<Clause>) units.clone();
				for (Clause clause : iteratedUnitClause) {
					clone.remove(clause);
				}
				iter = clone.iterator();
			}
		}
		this.units.clear();
		return emptyClause;

	}

	public Clause unitPropagation(int level, Stack<Variable> stack, Variable nextVar) {
		Clause emptyClause = null;
		if (level == 0) {
			for (Clause clause : clauses) {
				if (clause.getState() == ClauseState.UNIT) {
					if (!units.contains(clause)) {
						units.add(clause);
					}
				}
			}
		} else if (this.units.isEmpty()) {
			emptyClause = nextVar.assign(true, this.variables, units, level, stack);
			if (emptyClause != null)
				return emptyClause;
		}

		Vector<Clause> clone = (Vector<Clause>) this.units.clone();
		Iterator<Clause> iter = clone.iterator();
		Vector<Clause> iteratedUnitClause = new Vector<>();
		Integer literal = 0; // the unassigned literal

		while (iter.hasNext()) {
			Clause currentUnitClause = iter.next();
			iteratedUnitClause.add(currentUnitClause);
			// in case of the currentUnitClause be set to be other state before iterated
			if(currentUnitClause.getState().equals(ClauseState.UNIT)){
				literal = currentUnitClause.getUnassigned(variables);
				if (literal > 0) {
					emptyClause = variables.get(Math.abs(literal)).assign(true, this.variables, units, level, stack);
				} else if (literal < 0) {
					emptyClause = variables.get(Math.abs(literal)).assign(false, this.variables, units, level, stack);
				} else {
					System.err.println("unit clause is "+currentUnitClause + "");
					System.err.println("found the literal 0");
				}
				if (emptyClause != null) {
					break;
				}
			}
			
			
			/*
			 * get clone of units, remove clauses which are already iterated.
			 * reassign the iterator.
			 */
			if (!iter.hasNext()) {
				clone = (Vector<Clause>) units.clone();
				for (Clause clause : iteratedUnitClause) {
					clone.remove(clause);
				}
				iter = clone.iterator();
			}
		}
		this.units.clear();
		return emptyClause;
	}

	public boolean containsNotSAT() {
		boolean result = false;
		for (Clause clause : clauses) {
			if (clause.getState().equals(ClauseState.SUCCESS)) {
				result = true;
				for (Integer literal : clause.getLiterals()) {
					if ((this.variables.get(Math.abs(literal)).getState().equals(State.TRUE) && literal > 0)
							|| (this.variables.get(Math.abs(literal)).getState().equals(State.FALSE) && literal < 0)) {
						result = false;
						//clause.setState(ClauseState.SAT);
						break;
					}
				}
			}
			if(result) return result;
		}
		return result;
	}

	public Vector<Clause> getClauses() {
		return clauses;
	}

	/**
	 * 
	 * @param firstUIP
	 * @param level
	 *            where the conflict happened
	 */
	public void addFirstUIP(Clause firstUIP, int level) {
		/*
		 * 1. increase the activity of each variable 
		 * 2. sort 1UIP descending by level of each variable . 
		 * 2. the variable with highest level should be set to be open and be placed at the first position
		 * 3. set the first and second literal as watched literal.
		 * 		(if there is only one literal in this firstUIP, then first and second point to the same literal)
		 * 4. add 1UIP to watched list of first and second variable 
		 * 5. because this variable need to be reassigned, so clean this variable
		 */
		
		Variable var = null;
		int indexOfVarWithHighestLevel = 0 ; // where is the variable with highest level
		
		
		
//		for(int i = 0 ; i <firstUIP.getLiterals().size(); i++){
//			var = variables.get(Math.abs(firstUIP.getLiterals().get(i)));
//			var.increaseActivity();
//			if (var.getLevel() == level) {
//				var.setState(State.OPEN);
//				var.getWatched().stream().forEach(c -> c.setState(ClauseState.SUCCESS));
//				indexOfVarWithHighestLevel = i;
//			}
//		}
//		
//		// make sure that variable with highest level in the first position
//		if(indexOfVarWithHighestLevel != 0){
//			Integer temp = firstUIP.getLiterals().get(indexOfVarWithHighestLevel);
//			firstUIP.getLiterals().set(indexOfVarWithHighestLevel, firstUIP.getLiterals().get(0));
//			firstUIP.getLiterals().set(0, temp);
//		}
		
		// sort 1UIP descending by level of each variable .
		Collections.sort(firstUIP.getLiterals(), (lit1, lit2) -> {
			return Integer.compare(variables.get(Math.abs(lit2)).getLevel(),variables.get(Math.abs(lit1)).getLevel()) ;
		});
		
		// 1. increase the activity of each variable 
		// 2. the variable with highest level should be set to be open
		// 3. clean this variable
		firstUIP.getLiterals().stream()
		.map(lit -> variables.get(Math.abs(lit)))
		.forEach(v -> {
			v.increaseActivity();
			if (v.getLevel() == level) {
				//v.setState(State.OPEN);
				//v.getWatched().stream().forEach(c -> c.setState(ClauseState.SUCCESS));
				//v.clean(variables, this);
			}
		});;
		
		// 3. set the first and second literal as watched literal.
		//  	(if there is only one literal in this firstUIP, then first and second point to the same literal)
		firstUIP.setLit1(firstUIP.getLiterals().get(0));
		variables.get(Math.abs(firstUIP.getLiterals().get(0))).getWatched().add(firstUIP);
		if(firstUIP.getLiterals().size() == 1){
			firstUIP.setLit2(firstUIP.getLiterals().get(0));
		}else{
			firstUIP.setLit2(firstUIP.getLiterals().get(1));
			variables.get(Math.abs(firstUIP.getLiterals().get(1))).getWatched().add(firstUIP);
		}
		
		/* add to clause Set */
		this.clauses.addElement(firstUIP);
		//System.out.println("add first UIP " + firstUIP);
		/* add to unit clause list */
		firstUIP.setState(ClauseState.UNIT);
		units.add(firstUIP);
	}

	@Override
	public String toString() {
		return clausesToString() + "\n\n" + varsToString();
	}

	/**
	 * Returns all clauses as string representation.
	 * 
	 * @return a string representation of all clauses.
	 */
	public String clausesToString() {
		String res = "";
		for (Clause clause : clauses)
			res += clause + "\n";
		return res;
	}

	/**
	 * Returns all variables as string representation.
	 * 
	 * @return a string representation of all variables.
	 */
	public String varsToString() {
		String res = "";
		for (int i = 1; i <= varNum; i++)
			res += "Variable " + i + ": " + variables.get(i) + "\n\n";
		return res;
	}

	public HashMap<Integer, Variable> getVariables() {
		return variables;
	}

}