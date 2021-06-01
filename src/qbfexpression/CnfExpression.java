package qbfexpression;
import java.util.List;

public interface CnfExpression {
	public int getn();
	public boolean hasQuantifier();
	public void addcnf(Disjunction c);
	public void addquantifier(Quantifier q);
	// methods related to quantifiers
	public Quantifier peek();
	public int maxSameQuantifier(boolean type);
	public List<Quantifier> peek(int count, boolean type);
	public void dropquantifier();
	public void dropquantifier(int v);
	// methods related to variable assignment
	public boolean set(int v);
	public void setSatisfied(boolean val);
	// simplification and undo
	public void simplify();
	public CnfExpression duplicate();
	public void undo();
	public void commit();
	// pre-processing
	public void normalize();
	// evaluate
	public int evaluate();
}
