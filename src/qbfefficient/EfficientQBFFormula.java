package qbfefficient;

import java.util.List;

import qbfexpression.Conflict;
import qbfexpression.Quantifier;

public interface EfficientQBFFormula {
	// method related to clauses
	public void addClause(List<Integer> c);
	public void learn(List<Integer> c);
	public Conflict getReason();
	// method related to set literal
	public void set(int v);
	public void undo();
	public void simplify();
	public int evaluate();
	// method related to quantifier
	public Quantifier peek();
	public void addQuantifier(Quantifier q);
	public int depth(int v);
	public boolean isMax(int v);
	// normalized
	public void normalize(int type);
}
