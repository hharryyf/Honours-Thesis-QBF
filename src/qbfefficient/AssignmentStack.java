package qbfefficient;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import utilstructure.Pair;

public class AssignmentStack {
	protected LinkedList<Pair<Integer, Pair<Character, Integer>>> assignment;
	protected Set<Integer> literal;
	// literal, (type, id)
	protected Map<Integer, Pair<Character, Integer>> unit;
	public AssignmentStack() {
		this.literal = new HashSet<>();
		this.assignment = new LinkedList<>();
		this.unit = new HashMap<>();
	}
	/**
	 * 
	 * @param v :: integer, a literal
	 * @return boolean, whether the literal is in the current assignment
	 */
	public boolean hasLiteral(int v) {
		return literal.contains(v);
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
    public void assign(int v, char type, int id) {
    	if (hasVar(v)) MyError.abort("reassign variable");
    	this.literal.add(v);
    	this.assignment.add(new Pair<>(v, new Pair<>(type, id)));
    	this.unit.put(v, new Pair<>(type, id));
	}
    /**
     * 
     * @return the last assignment :: pair<int, pair<char, int>>, (literal, (type, clause id))
     */
    public Pair<Integer, Pair<Character, Integer>> peek() {
    	return this.assignment.peekLast();
    }
    
    /**
     * peek and remove
     * @return last assignment
     */
    public Pair<Integer, Pair<Character, Integer>> unassign() {
    	if (this.literal.isEmpty()) MyError.abort("unassign empty assignment");
    	this.literal.remove(this.peek().first);
    	this.unit.remove(this.peek().first);
    	return this.assignment.pollLast();
    }
    
    public Pair<Character, Integer> getUnit(int l) {
    	if (this.unit.containsKey(l)) {
    		return this.unit.get(l);
    	}
    	
    	MyError.abort(l + " is not unit");
    	return null;
    }
}
