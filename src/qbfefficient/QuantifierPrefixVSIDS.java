package qbfefficient;

import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;

import qbfexpression.Quantifier;
import utilstructure.Pair;

public class QuantifierPrefixVSIDS {
	private boolean normalized = false;
	protected int[] depth;
	protected Quantifier[] quantifier;
	protected double[] score;
	protected List<TreeSet<Pair<Double, Integer>>> heuristic;
	public QuantifierPrefixVSIDS(int n) {
		int i;
		this.depth = new int[n + 1];
		this.quantifier = new Quantifier[n + 1];
		this.score = new double[n + 1];
	    this.heuristic = new ArrayList<>();
	    for (i = 0 ; i <= n; ++i) {
	    	this.depth[i] = 0;
	    	this.score[i] = 0.0;
	    }
	}
	
	public void normalized() {
		int i, mx = -1;
		for (i = 1; i < this.depth.length; ++i) {
			mx = Math.max(mx, depth[i]);
		}
		
		for (i = 0; i <= mx; ++i) {
			this.heuristic.add(new TreeSet<>());
		}
		
		for (i = 1; i < this.quantifier.length; ++i) {
			this.heuristic.get(this.depth[i]).add(new Pair<>(score[i], i));
		}
		
		this.normalized = true;
	}
	
	public void remove(int q) {
		if (!this.normalized) MyError.abort("cannot remove quantifier when norlalized is false");
		if (q < 0) q = -q;
		int d = this.depth[q];
		this.heuristic.get(d).remove(new Pair<Double, Integer>(score[q], q));
	}
	
    public void insert(int q) {
    	if (!this.normalized) MyError.abort("cannot call this insertion method when norlalized is false");
    	if (q < 0) q = -q;
    	int d = this.depth[q];
    	this.heuristic.get(d).add(new Pair<Double, Integer>(score[q], q));
    }
	
    /**
     * 
     * @param q, quantifier id
     * @param d, depth
     */
    
	public void insert(Quantifier q, int d) {
		this.quantifier[q.getVal()] = q;
		this.depth[q.getVal()] = d;
	}
	
	/**
	 * 
	 * @return peek the quantifier followed the VSIDS heuristic
	 */
	
	public Quantifier peek() {
		if (!this.normalized) MyError.abort("cannot peek quantifier when norlalized is false");
		int i;
		Pair<Double, Integer> ret = null;
		for (i = 0 ; i < heuristic.size(); ++i) {
			if (!heuristic.get(i).isEmpty()) {
				Pair<Double, Integer> candidate = heuristic.get(i).last();
				if (ret != null && this.quantifier[ret.second].isMax() != this.quantifier[candidate.second].isMax()) {
					break;
				}
				
				if (ret == null) {
					ret = heuristic.get(i).last();
				} else if (ret.compareTo(candidate) < 0) {
					ret = candidate;
				}
			}
		}
		
		if (ret == null) MyError.abort("invariant broken, no quantifier remaining");
		return this.quantifier[ret.second];
	}
	
	/**
	 * 
	 * @param q
	 * @param v :: new score of q
	 */
	
	public void updateWeight(int q, double v) {
		if (!this.normalized) MyError.abort("cannot update VSIDS score when norlalized is false");
		if (q < 0) q = -q;
		this.remove(q);
		this.score[q] = v;
		this.insert(q);
	}
}	
