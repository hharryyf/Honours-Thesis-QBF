package qbfexpression;

import java.util.List;

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
}
