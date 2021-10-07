package qbfexpression;

import java.util.List;
import java.util.TreeMap;

public abstract class QuantifierBlock {
	public int quantifiercount = 0, unicount = 0;
	// a priority of the quantifier
	public Quantifier[] quantifiers;
	public int[] order;
	public int[] poscount;
	public int[] negcount;
	public boolean[] isexist;
	public QuantifierBlock(int n) {
		this.quantifiers = new Quantifier[n+1];
		this.quantifiercount = n;
		this.poscount = new int[n+1];
		this.negcount = new int[n+1];
		this.order = new int[n+1];
		this.isexist = new boolean[n+1];
		for (int i = 0 ; i <= n; ++i) this.isexist[i] = true;
	}
	
	public abstract void insert(Quantifier q, boolean normalized);
	public abstract boolean hasQuantifier(int v);
	public abstract Quantifier peek();
	public abstract int maxSameQuantifier(boolean type);
	public abstract List<Quantifier> peek(int count, boolean type);
    public abstract void dropQuantifier();
	public abstract void dropQuantifier(int v);
	public abstract void updatePositive(int v, int inc);
	public abstract void updateNegative(int v, int inc);
	public abstract int size();
	public abstract boolean istopMax();
	public abstract void prepend(Quantifier q);
	protected abstract String toString(TreeMap<Integer, Integer> squeeze);

	public abstract boolean isOuter(int v);
	public abstract List<Integer> getUniverse();
}
