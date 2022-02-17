package qbfefficient;

import java.util.HashMap;
import java.util.Map;

public class SatisfiedCounter {
	private String lm = new String("SATISFIED_COUNTER");
	private int count = 0, dim = 0;
	protected Map<Integer, Integer> sat;
	public SatisfiedCounter() {
		this.sat = new HashMap<>();
		this.count = 0;
	}
	
	public void setDim(int dim) {
		this.dim = dim;
	}
	
	/**
	 * 
	 * @param v add the sat counter for clause v
	 */
	
	public boolean addsat(int v) {
		if (sat.getOrDefault(v, 0) == 0) {
			this.count++;
			sat.put(v, 1);
			return true;
		} 
		
		sat.put(v, sat.get(v) + 1);
		return false;
	}
	
	/**
	 * 
	 * @param id
	 * @return is the clause id sat :: boolean
	 */
	public boolean issat(int id) {
		return sat.getOrDefault(id, 0) > 0;
	}
	
	/**
	 * 
	 * @param decrement the sat counter of clause v
	 */
	
	public void removesat(int v) {
		int tol = sat.getOrDefault(v, 0);
		if (tol == 0) MyLog.log(lm, 0, "remove satisfied clause before adding in " + (this.dim == 1 ? "LEARNED_CLAUSE" : "ORIGINAL_CLAUSE") + " " + this.sat + " clauseid: " + v);
		
		if (tol == 1) {
			this.count--;
		}
		
		sat.put(v, tol - 1);
	}
	
	public int getDim() {
		return this.dim;
	}
	
	/**
	 * 
	 * @return number of sat clauses :: integer
	 */
	public int satClause() {
		return this.count;
	}
}
