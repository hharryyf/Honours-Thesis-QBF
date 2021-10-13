package qbfefficient;

import java.util.List;

public abstract class ConflictSolution implements Comparable<ConflictSolution> {
	protected int opencount;
	protected boolean satisfied;
	public ConflictSolution() {
		this.opencount = 0;
	}
	public abstract void addLiteral(EfficientQBFFormula f, TwoWatchedLiteralClause c);
	public abstract void addAssignment(EfficientQBFFormula f, List<Integer> c);
	public abstract void resolve(ConflictSolution other, int v, EfficientQBFFormula f);
	public abstract int size();
	public abstract boolean contains(int v);
	public boolean isSolution() {
		return this.satisfied;
	}
	// drop a literal, unit case
	public abstract void drop(EfficientQBFFormula f, int v);
}
