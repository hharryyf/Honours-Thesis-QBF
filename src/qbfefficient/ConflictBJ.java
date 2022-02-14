package qbfefficient;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class ConflictBJ extends ConflictSolution {
	private String lm = new String("CONFLICT_SOLUTION_BJ");
	private Set<Integer> literal;
	public ConflictBJ(boolean sat) {
		this.satisfied = sat;
		this.literal = new HashSet<>();
	}
	
	@Override
	public void addLiteral(EfficientQBFFormula f, TwoWatchedLiteralClause c) {
		for (Integer v : c.existential) {
			literal.add(-v);
		}
	}
	
	@Override
	public int size() {
		return this.literal.size();
	}
	
	@Override
	public boolean contains(int v) {
		return this.literal.contains(v);
	}
	
	@Override
	public void resolve(ConflictSolution other, int v, EfficientQBFFormula f) {
		if (other.isSolution() != this.isSolution()) MyLog.log(lm, 0, "resolve solution with conflict");
		if (other.getClass() != ConflictBJ.class) MyLog.log(lm, 0, "resolve with different conflict type");
		if (this.size() >= other.size()) {
			for (Integer li : ((ConflictBJ) other).literal) {
				this.literal.add(li);
			}
		} else {
			for (Integer li : this.literal) {
				((ConflictBJ) other).literal.add(li);
			}
			this.literal = ((ConflictBJ) other).literal;
		}
		this.literal.remove(v);
		this.literal.remove(-v);
	}
	
	@Override
	public void drop(EfficientQBFFormula f, int v) {
		this.literal.remove(v);
	}

	@Override
	public void addAssignment(EfficientQBFFormula f, List<Integer> c) {
		for (Integer v : c) this.literal.add(v);
	}

	@Override
	public int compareTo(ConflictSolution o) {
		Integer it = new Integer(this.literal.size());
		Integer it2 = new Integer(o.size());
		return it.compareTo(it2);
	}
	
	public String toString() {
		return this.literal.toString();
	}
}
