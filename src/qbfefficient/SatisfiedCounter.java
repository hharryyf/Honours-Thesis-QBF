package qbfefficient;

import java.util.HashMap;
import java.util.Map;

public class SatisfiedCounter {
	protected String lm = new String("SATISFIED_COUNTER");
	private int count = 0;
	protected Map<Integer, Integer> sat;
	public SatisfiedCounter() {
		this.sat = new HashMap<>();
		this.count = 0;
	}
	
	/**
	 * 
	 * @param v add the sat counter for clause v
	 */
	
	public void addsat(int v) {
		if (sat.getOrDefault(v, 0) == 0) {
			this.count++;
			sat.put(v, 1);
		} else {
			sat.put(v, sat.get(v) + 1);
		}
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
		if (tol == 0) MyLog.log(lm, true, "remove satisfied clause before adding in");
		
		if (tol == 1) {
			this.count--;
		}
		
		sat.put(v, tol - 1);
	}
	
	/**
	 * 
	 * @return number of sat clauses :: integer
	 */
	public int satClause() {
		return this.count;
	}
}
