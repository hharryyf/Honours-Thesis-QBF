package qbfefficient;

import java.util.List;
import qbfexpression.Quantifier;

public interface EfficientQBFFormula {
	// method related to clauses
	public void addClause(List<Integer> c);
	public void learn(List<Integer> c);
	public ConflictSolution getReason();
	// method related to set literal
	public void set(int v);
	public void undo(ConflictSolution reason);
	public void simplify();
	public int evaluate();
	// method related to quantifier
	public Quantifier peek();
	public void addQuantifier(Quantifier q);
	public boolean isassigned(int v);
	public TwoWatchedLiteralClause unitId(int v);
	public int depth(int v);
	public boolean isMax(int v);
	// normalized
	public void normalize(int type);
}
