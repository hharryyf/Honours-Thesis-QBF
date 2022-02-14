package qbfefficient;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;


import utilstructure.Pair;

public class AssignmentStack {
	private String lm = new String("ASSIGNMENT_STACK");
	protected LinkedList<Pair<Integer, AssignId>> assignment;
	protected Map<Integer, Integer> literal;
	// literal, (dimension, type, id)
	private Map<Integer, AssignId> unit;
	public AssignmentStack() {
		this.literal = new HashMap<>();
		this.assignment = new LinkedList<>();
		this.unit = new HashMap<>();
	}
	/**
	 * 
	 * @param v :: integer, a literal
	 * @return boolean, whether the literal is in the current assignment
	 */
	public boolean hasLiteral(int v) {
		return literal.containsKey(v);
	}
	/**
	 * 
	 * @param v :: integer, variable
	 * @return boolean, whether the variable is assigned positively/negatively
	 */
	public boolean hasVar(int v) {
		return hasLiteral(v) || hasLiteral(-v);
	}
	/**
	 * 
	 * @param v :: integer, a literal
	 * @param type :: character, the type of assignment (unit or branching)
	 * for this variable, 'U' means unit in original formula, 'E' means unit in lemma, 'A' means unit in model
	 * 'N' means branching variable
	 * @param id :: integer, clause related to this assignment, if type = N,  id = -1
	 */
	
	
    public void assign(int v, int dimension, char type, int id) {
    	if (hasVar(v)) MyLog.log(lm, 0, "reassign variable");
    	this.literal.put(v, this.literal.size());
    	this.assignment.add(new Pair<>(v, new AssignId(dimension, type, id)));
    	if (type != 'N') {
    		this.unit.put(v, new AssignId(dimension, type, id));
    	}
	}
    /**
     * 
     * @return the last assignment :: pair<int, pair<char, int>>, (literal, (type, clause id))
     */
    public Pair<Integer, AssignId> peek() {
    	return this.assignment.peekLast();
    }
    
    /**
     * peek and remove
     * @return last assignment
     */
    public Pair<Integer, AssignId> unassign() {
    	if (this.literal.isEmpty()) MyLog.log(lm, 0, "unassign empty assignment");
    	this.literal.remove(this.peek().first);
    	if (this.peek().second.type != 'N') {
    		this.unit.remove(this.peek().first);
    	}
    	
    	MyLog.log(lm, 3, "unassign ", this.assignment.getLast().first);
    	
    	return this.assignment.pollLast();
    }
    
    public AssignId getUnit(int l) {
    	if (this.unit.containsKey(l)) {
    		return this.unit.get(l);
    	}
    	
    	// MyError.abort(l + " is not unit");
    	return null;
    }
}
