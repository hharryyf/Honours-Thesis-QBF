package qbfefficient;

import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;

public class TwoWatchedLiteralClause implements Comparable<TwoWatchedLiteralClause>{
	protected List<Integer> universal;
	protected List<Integer> existential;
	protected TreeSet<Integer> watchedE, watchedU;
	protected int id;
	private TwoWatchedLiteralFormula f;
	public TwoWatchedLiteralClause() {
		this.universal = new ArrayList<>();
		this.existential = new ArrayList<>();
		this.watchedE = new TreeSet<>();
		this.watchedU = new TreeSet<>();
	}
	
	public void setId(int id) {
		this.id = id;
	}
	
	public void setFormula(TwoWatchedLiteralFormula f) {
		if (this.f != null) MyError.abort("invalid setFormula");
		this.f = f;
	}
	
	/**
	 * @param v a literal, either positive or negative
	 * invariant: the literal inserted in must follow the increasing quantifier order
	 */
	public void addLiteral(int v) {
		if (f.quantifier.quantifier[Math.abs(v)].isMax()) {
			this.existential.add(v);
		} else {
			this.universal.add(v);
		}
	}
	
	@Override
	public int compareTo(TwoWatchedLiteralClause arg0) {
		Integer id1 = new Integer(id);
		return id1.compareTo(arg0.id);
	}
	
	public String toString() {
		return this.existential.toString().concat(" " + this.universal.toString());
	}
}
