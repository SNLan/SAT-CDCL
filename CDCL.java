package satsolving.blatt06.dataStructure;

import java.util.Iterator;
import java.util.Stack;
import java.util.Vector;

import satsolving.blatt06.dataStructure.Clause.ClauseState;
import satsolving.blatt06.dataStructure.Variable.State;

public class CDCL {

	// the instance need to be processed
	private ClauseSet instance;

	// store the variables that been assigned. The decision variables and UP
	// variables
	// by backtracking we can get the level of the variable
	private Stack<Variable> stack = new Stack<>();

	public CDCL(ClauseSet instance) {
		this.instance = instance;
	}

	/**
	 * Resolution method
	 * 
	 * @param c1
	 * @param c2
	 * @return learned clause
	 */
	private Clause resolve(Clause conflict, Clause reason) {
		System.out.println("conflict: " + conflict + "\n" + "reason: " + reason + "\n");
		reason.setState(ClauseState.SUCCESS);
		// Variable lastVar = this.stack.pop();
		Vector<Integer> temp = new Vector<>();
		Iterator<Integer> confIte = conflict.getLiterals().iterator();
		Iterator<Integer> reaIte = reason.getLiterals().iterator();
		while (confIte.hasNext()) {
			temp.add(confIte.next());
		}
		while (reaIte.hasNext()) {
			Integer intRea = reaIte.next();
			Integer negIntRea = intRea - 2 * intRea;
			if (temp.contains(negIntRea)) {
				temp.remove(negIntRea);
			} else if (!temp.contains(intRea)) {
				temp.addElement(intRea);
			}
		}
		return new Clause(temp);
	}

	/**
	 * calculate the first UIP
	 * 
	 * @param conflict:
	 *            empty clause
	 * @param reason:
	 *            reason clause
	 * @return firstUIP
	 */
	private Clause get1UIP(Clause conflict, Clause reason) {
		Clause firstUIP = null;
		/* the conflict were happened in the highest level of conflict clause */
		int happendLevel = conflict.getHighestLevel(this.instance.getVariables());
		conflict.setState(ClauseState.SUCCESS);
		firstUIP = resolve(conflict, reason);
		Variable lastVar;
		while (!firstUIP.isFirstUIP(happendLevel, this.instance.getVariables())) {
			lastVar = stack.pop();
			System.out.println(" stack : pop the elements " + lastVar);
			// if 1UIP does not contain this variable, then clean this variable and continue pop next variabel
			if(!firstUIP.containsVar(lastVar)){
				lastVar.clean(this.instance.getVariables(),this.instance);
				continue;
			}
			firstUIP = resolve(firstUIP, lastVar.getResaon());
			lastVar.clean(this.instance.getVariables(),this.instance);
		}
		return firstUIP;
	}

	/**
	 * use the Stack and the reason of conflict clause to
	 * 
	 * @param conflict:
	 *            empty clause
	 * @return backtracking level
	 */
	private int analyseConflict(Clause conflict) {
		int happendLevel = conflict.getHighestLevel(this.instance.getVariables());
		// if the current decision level is 0 then return -1
		if (happendLevel == 0)
			return -1;
		/* the backtracking level */
		int backLevel = 0;
		Variable lastVar = stack.pop();
		System.out.println(" stack : pop the elements " + lastVar);
		Clause firstUIP = get1UIP(conflict, lastVar.getResaon());
		// clean all of the state of this variable
		lastVar.clean(this.instance.getVariables(),this.instance);

		/* find the backtracking level */
		int varLevel; // the level of each variable
		for (Integer literal : firstUIP.getLiterals()) {
			// the level of each variable
			varLevel = this.instance.getVariables().get(Math.abs(literal)).getLevel();
			if (varLevel != happendLevel && varLevel > backLevel) {
				// biggest level is the backtracking level
				backLevel = varLevel;
			}
		}
		
		/* add to clause set */
		this.instance.addFirstUIP(firstUIP, happendLevel);
		// this.instance.addFirstUIP(firstUIP,lastVar);

		System.out.println("1UIP result = " + firstUIP);

		/*
		 * another thing need to be done: pop and clean variable until the variable with highest level,
		 * which is a decision variable(decision )
		 */
		// bug here
		Variable var = null;
		while (!stack.isEmpty()) {
			var = stack.peek();
			if(var.getLevel() == happendLevel){
				stack.pop();
				var.clean(this.instance.getVariables(), this.instance);
			}else{
				break;
			}
		}
		System.out.println(" stack : pop the elements " + lastVar);
		return backLevel;

	}

	public boolean solve() {
		// backtracking level
		int level = 0;
		/* next variable need to be assigned */
		Variable nextVar = null;
		boolean flag = true;
		while (flag) {
			Clause conflict = this.instance.unitPropagation(level, this.stack, nextVar);
			// if the conflict clause(empty clause) exist.
			if (conflict != null) {
				System.out.println("conflict clause is " + conflict);
				level = analyseConflict(conflict);
				if (level == -1) {
					return false;
				}
				System.out.println("backtracking level is " + level);
				// variables who's level greater then backtracking level should
				// be pop from stack
				popVar(level);
			} else {
				// if the empty clause does not exist.
				// see if there are other clause in this clauseSet, if yes
				// getNextVar to make decision if no return SAT.
				boolean existNotSATClauses = this.instance.containsNotSAT();
				if (existNotSATClauses) {
					level++;
					nextVar = getNextVar();
					System.out.println("choose the next variable : " + nextVar + " now level is at " + level);
					if(nextVar.getId() == 42){
						System.out.println("debug here");
					}
				} else {
					return true;
				}
			}
		}
		return false;
	}

	private void popVar(int level) {
		while (!stack.isEmpty()) {
			Variable popVar;
			if (stack.peek().getLevel() > level) {
				popVar = stack.pop();
				//System.out.println(" stack : pop the elements " + popVar);
				popVar.clean(this.instance.getVariables(),this.instance);
			} else {
				break;
			}
		}
	}

	/**
	 * return the next variable with highest activity which should be assigned
	 * 
	 * @return next variable
	 */
	private Variable getNextVar() {
		Variable next;
		next = this.instance.getVariables().entrySet().stream()
				.filter(entry -> entry.getValue().getState() == Variable.State.OPEN)
				.max((e1, e2) -> Float.compare(e1.getValue().getActivity(), e2.getValue().getActivity())).get()
				.getValue();
		next.decreaseActivity();
		return next;
	}

	/**
	 * whether a literal(could be positive or negative) return TRUE or FALSE
	 * 
	 * @param literal
	 * @return True, if this literal represent TRUE. False, if this literal
	 *         represent FALSE
	 */
	public boolean isSAT(Integer literal) {
		if ((this.instance.getVariables().get(Math.abs(literal)).equals(State.TRUE) && literal > 0)
				|| (this.instance.getVariables().get(Math.abs(literal)).equals(State.FALSE) && literal < 0)) {
			return true;
		}
		return false;
	}

	@Override
	public String toString() {
		return  "STACK "+this.stack.size()+" : \n" + this.stack.toString();
		//return "INSTANCE: \n" + this.instance + "\n" + "STACK "+this.stack.size()+" : \n" + this.stack.toString();
	}

}
