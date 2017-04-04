package satsolving.blatt06.dataStructure;

import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Vector;
import java.util.function.Function;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import satsolving.blatt06.dataStructure.Variable.State;

/**
 * A clause.
 * 
 */
public class Clause {
	/* Literals of the clause */
	private Vector<Integer> literals;

	private Integer lit1;
	private Integer lit2;

	/* Enumeration state of Clause */
	public enum ClauseState {
		SAT, EMPTY, UNIT, SUCCESS
	}

	/* the state of clause */
	private ClauseState state;

	/**
	 * Creates a new clause with the given literals.
	 * 
	 * @param literals
	 *            literals of the clause
	 * @param variables
	 */
	public Clause(Vector<Integer> literals, HashMap<Integer, Variable> variables) {
		this.literals = literals;

		literals.stream().map(id -> Math.abs(id)).forEach(id -> {
			Variable var = null;
			if (!variables.containsKey(id)) {
				var = new Variable(id);
				variables.put(id, var);
			} else {
				var = variables.get(id);
			}
			var.setActivity(var.getActivity() + 1);
		});
		// init watched literal and return a state
		this.state = initWatch(variables);
	}

	public Clause(Vector<Integer> literals) {
		this.literals = literals;
	}

	/**
	 * Returns the literals of this clause.
	 * 
	 * @return literals of this clause
	 */
	public Vector<Integer> getLiterals() {
		return literals;
	}

	/**
	 * Returns an unassigned literal of this clause.
	 * 
	 * @param variables
	 *            variable objects
	 * @return an unassigned literal, if one exists, 0 otherwise
	 */
	public int getUnassigned(HashMap<Integer, Variable> variables) {

		for (Integer l : literals) {
			if ((l == this.lit1 || l == this.lit2) && variables.get(Math.abs(l)).getState().equals(State.OPEN)) {
				return l;
			}
		}
		return 0;

	}

	public ClauseState initWatch(HashMap<Integer, Variable> variables) {
		if (this.literals.size() == 1) {
			this.lit1 = lit2 = this.literals.get(0);
			int id = Math.abs(this.literals.get(0));
			if (!variables.containsKey(id)) {
				variables.put(id, new Variable(id));
			}
			variables.get(Math.abs(this.literals.get(0))).getWatched().add(this);
			return ClauseState.UNIT;
		} else if (this.literals.size() == 0) {
			return ClauseState.EMPTY;
		} else {
			// set the init pointer
			this.lit1 = this.literals.get(0);
			this.lit2 = this.literals.get(1);
			// add this clause to the watched list of variables
			variables.get(Math.abs(lit1)).getWatched().add(this);
			variables.get(Math.abs(lit2)).getWatched().add(this);
			return ClauseState.SUCCESS;
		}
	}

	public ClauseState reWatch(HashMap<Integer, Variable> variables, int beMovedLit, Vector<Clause> movedClause) {
		int otherWatchedLit = beMovedLit == this.lit1 ? lit2 : lit1;
		/* the assigned literal in this clause */
		int unAssignedLit = 0;
		ClauseState retState = null;

		// find the literal that are not the watched literal and not assigned
		for (Integer l : literals) {
			if (l != this.lit1 && l != this.lit2 && variables.get(Math.abs(l)).getState().equals(State.OPEN)) {
				unAssignedLit = l;
				break;
			}
		}

		/* if didn't find, set the state of this clause */
		// depends on the state of the rest variables,
		if (unAssignedLit == 0) {
			for (Integer literal : literals) {
				// any variable(except watched literal) was assigned to be true,
				// then this clause are SAT
				if (literal != this.lit1 && literal != this.lit2) {
					if (checkLiteralState(literal, variables).equals(State.TRUE)) {
						retState = ClauseState.SAT;
						break;
					}
				}
			}
			// any of the variables are false, so retState is null
			if (retState == null) {
				// if a clause like (32,-32,-4), -4 is FALSE, then whatever 32 be assigned, this clause is always SAT
				if (variables.get(Math.abs(otherWatchedLit)).getState() == State.TRUE || beMovedLit == -otherWatchedLit) {
					retState = ClauseState.SAT;
				} else if (variables.get(Math.abs(otherWatchedLit)).getState() == State.FALSE) {
					retState = ClauseState.EMPTY;
				} else if (variables.get(Math.abs(otherWatchedLit)).getState() == State.OPEN) {
					retState = ClauseState.UNIT;
					// variables.get(Math.abs(otherWatchedLit)).getWatched().add(this);
				}
			}
		} else {
			/*
			 * found, move the pointer forward, watched list of variable should
			 * add this clause
			 */
			if (this.lit1 == beMovedLit) {
				this.lit1 = unAssignedLit;
			} else {
				this.lit2 = unAssignedLit;
			}
			movedClause.addElement(this);
			variables.get(Math.abs(unAssignedLit)).getWatched().add(this);
			retState = ClauseState.SUCCESS;
		}
		return retState;
	}

	public int getHighestLevel(HashMap<Integer, Variable> variables) {
		return this.literals.stream().map(l -> variables.get(Math.abs(l)).getLevel()).max(Integer::compareTo).get();
	}

	/**
	 * check if this clause contains only one variable with highest level
	 * 
	 * @param level
	 * @return
	 */
	public boolean isFirstUIP(int level, HashMap<Integer, Variable> variables) {
		boolean appearOnce = false;
		for (Integer integer : literals) {
			if (variables.get(Math.abs(integer)).getLevel() == level) {
				if (!appearOnce) {
					appearOnce = true;
				} else {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * check state of parameter literal in this clause
	 * 
	 * @param lit
	 * @param variables
	 * @return OPEN or TRUE or FALSE
	 */
	public State checkLiteralState(Integer lit, HashMap<Integer, Variable> variables) {
		if (variables.get(Math.abs(lit)).getState().equals(State.OPEN)) {
			return State.OPEN;
		} else if ((variables.get(Math.abs(lit)).getState().equals(State.TRUE) && lit > 0)
				|| (variables.get(Math.abs(lit)).getState().equals(State.FALSE) && lit < 0)) {
			return State.TRUE;
		} else {
			return State.FALSE;
		}
	}

	/**
	 * Returns true if this clause contains a variable
	 * 
	 * @param var
	 * @return
	 */
	public boolean containsVar(Variable var) {
		return this.getLiterals().stream().anyMatch(lit -> var.getId() == Math.abs(lit));
	}

	/**
	 * Return true, if a variable appears more then twice in this clause. like
	 * (-20,35,-35)
	 * 
	 * @param var
	 *            variable to be checked
	 * @return
	 */
	public boolean appearsMore(Variable var) {
		int count = 0;
		for (int i = 0; i < literals.size(); i++) {
			if (var.getId() == Math.abs(literals.get(i))) {
				count++;
			}
		}
		if (count > 1) {
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Returns the phase of the variable within this clause.
	 * 
	 * @param num
	 *            variable ID (>= 1)
	 * @return true, if variable is positive within this clause, otherwise false
	 */
	public boolean getPolarity(int num) {
		return literals.contains(num);
	}

	/**
	 * Returns the size of this clause.
	 * 
	 * @return size of this clause.
	 */
	public int size() {
		return literals.size();
	}

	public ClauseState getState() {
		return state;
	}

	public void setState(ClauseState state) {
		this.state = state;
	}

	public Integer getLit1() {
		return lit1;
	}

	public void setLit1(Integer lit1) {
		this.lit1 = lit1;
	}

	public Integer getLit2() {
		return lit2;
	}

	public void setLit2(Integer lit2) {
		this.lit2 = lit2;
	}

	@Override
	public String toString() {
		String res = "{ ";
		for (Integer i : literals)
			res += i + " ";
		return res + "}" + " - " + this.state;
	}
}