package satsolving.blatt06.dataStructure;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Optional;
import java.util.Stack;
import java.util.Vector;

import satsolving.blatt06.dataStructure.Clause.ClauseState;

/**
 * A variable.
 * 
 * @param <E>
 * 
 */
public class Variable {

	/* Assignment states of a variable */
	public enum State {
		TRUE, FALSE, OPEN
	};

	/* Current assignment */
	private State state;

	/* Variable ID (range from 1 to n) */
	private int id;

	/* Activity of the variable */
	private float activity = 0;

	/* the level in which this unit clause be assigned. */
	private int level;

	/*
	 * the reason why is a variable in this clause been assigned. Decision is
	 * null
	 */
	private Clause resaon = null;

	/*
	 * if the variable is now in a clause watched, then the clause is in this
	 * Vector
	 */
	private Vector<Clause> watched = new Vector<>();

	public Vector<Clause> getWatched() {
		return watched;
	}

	/**
	 * Creates a variable with the given ID.
	 * 
	 * @param id
	 *            ID of the variable
	 */
	public Variable(int id) {
		this.id = id;
		this.state = State.OPEN;
	}

	/**
	 * Returns the current assignment state of this variable.
	 * 
	 * @return current assignment state
	 */
	public State getState() {
		return state;
	}

	public void setState(State state) {
		this.state = state;
	}

	/**
	 * Returns the ID of this variable.
	 * 
	 * @return ID of this variable
	 */
	public int getId() {
		return id;
	}

	/**
	 * @param val
	 *            to be assign
	 * @param variables
	 *            the map of variables
	 * @param units
	 *            store the unit clause
	 * @return after assignments, if a clause is empty, then return this clause,
	 *         otherwise return null
	 */
	public Clause assign(boolean val, HashMap<Integer, Variable> variables, Vector<Clause> units, int level,
			Stack<Variable> stack) {
		// assign value to this variable
		if (val) {
			this.state = State.TRUE;
		} else {
			this.state = State.FALSE;
		}
		if (this.getId() == 32 && level == 4) {
			System.out.println("debug here");
		}

		this.level = level;
		stack.push(this);
		System.out.println("set variable " + this.getId() + " = " + this.state);
		Clause emptyClause = null;

		int beMovedLit;
		// store clause whose watched literal has been moved 
		Vector<Clause> movedClause = new Vector<>();
		ClauseState cState;
		// the watched list of this variable
		Iterator<Clause> iterator = getWatched().iterator();
		Clause c = null;
		while (iterator.hasNext()) {
			cState = null;
			c = iterator.next();
			// the literal in c should be moved, lit1 or lit2
			beMovedLit = Math.abs(c.getLit1()) == this.id ? c.getLit1() : c.getLit2();

			if (c.getState().equals(ClauseState.UNIT)) {
				if ((beMovedLit > 0 && val) || (beMovedLit < 0 && !val)) {
					cState = ClauseState.SAT;
					
					if(this.resaon == null){
						//this.resaon = c;
						Optional<Clause> optional = units.stream().filter(clause -> clause.getState().equals(ClauseState.UNIT)).findFirst();
						if(optional.isPresent()){
							this.resaon = optional.get();
						}
					}
				} else if ((beMovedLit > 0 && !val) || (beMovedLit < 0 && val)) {
					cState = ClauseState.EMPTY;
				}
			} else if (((beMovedLit > 0 && !val) || (beMovedLit < 0 && val)) && !c.getState().equals(ClauseState.SAT)) {
				cState = c.reWatch(variables, beMovedLit, movedClause);
				//if(cState.equals(ClauseState.UNIT)){
					System.out.println("after rewatch the  State of the " + c.toString() + " is " + cState);
				//}
			} else {
				c.setState(ClauseState.SAT);
			}

			if (cState == ClauseState.EMPTY) {
				c.setState(ClauseState.EMPTY);
				if (emptyClause == null) {
					emptyClause = c;
				}
			} else if (cState == ClauseState.UNIT) {
				c.setState(ClauseState.UNIT);
				units.add(c);
			} else if (cState == ClauseState.SAT) {
				c.setState(ClauseState.SAT);
			}
		}
		this.getWatched().removeAll(movedClause);
		return emptyClause;
	}

	/**
	 * clean the state, reason, level to the initial value the watched list
	 */
	public void clean(HashMap<Integer, Variable> variables, ClauseSet cs) {
		this.resaon = null;
		this.level = -1;
		this.state = State.OPEN;
		ClauseState newState = ClauseState.SUCCESS;

		cs.getClauses().stream().filter(clause -> clause.containsVar(this)).forEach(clause -> {
			// newState = ClauseState.SUCCESS;
			if (clause.getState() == ClauseState.SAT) {
				boolean flag = clause.getLiterals().stream().filter(lit -> Math.abs(lit) != this.id)
						.anyMatch(lit -> clause.checkLiteralState(lit, variables).equals(State.TRUE));
				if (flag) {
					clause.setState(ClauseState.SAT);
				}else if(clause.getLiterals().stream().filter(lit -> Math.abs(lit) != this.id)
						.allMatch(lit -> clause.checkLiteralState(lit, variables).equals(State.FALSE)
								&& !clause.appearsMore(this))){
					clause.setState(ClauseState.UNIT);
				}else {
					clause.setState(ClauseState.SUCCESS);
				}

			} else if (clause.getState() == ClauseState.UNIT) {
				// if we continual pop some elements, should check if those
				// elements exist in the same clause.
				// except this variable, if exists a variable with state OPEN,
				// then should be set to SUCCESS. otherwise, UNIT
				if (clause.getLiterals().stream().filter(lit -> Math.abs(lit) != this.id)
						.anyMatch(lit -> variables.get(Math.abs(lit)).getState().equals(State.OPEN))) {
					clause.setState(ClauseState.SUCCESS);
				} else {
					clause.setState(ClauseState.UNIT);
				}
			} else {
				clause.setState(ClauseState.SUCCESS);
			}
		});
		

	}

	public float getActivity() {
		return activity;
	}

	public void setActivity(float activity) {
		this.activity = activity;
	}

	/*
	 * increase activity by multi 1.1 if a new learned clause contains this
	 * variable
	 */
	public void increaseActivity() {
		this.activity *= 1.10;
	}

	/*
	 * decrease activity by multi 0.95 if this variable was chose by CDCL
	 * algorithmus
	 */
	public void decreaseActivity() {
		this.activity = (float) (this.activity * 0.95);
	}

	public int getLevel() {
		return level;
	}

	public void setLevel(int level) {
		this.level = level;
	}

	public Clause getResaon() {
		return resaon;
	}

	@Override
	public String toString() {
		String res = "[" + this.id + " - " + state + " - " + this.activity + " - " + this.level + " - " + this.resaon;
		return res + "]\n";
	}
}