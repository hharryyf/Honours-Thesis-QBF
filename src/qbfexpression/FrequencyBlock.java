package qbfexpression;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;
import utilstructure.Pair;

public class FrequencyBlock extends QuantifierBlock {
	// (order,quantifier)
	private TreeSet<Pair<Integer, Quantifier>> quantifier;
	public FrequencyBlock(int n) {
		super(n);
		this.quantifier = new TreeSet<>();
	}
	
	private boolean isMax(int val) {
		if (val < 0) val = -val;
		return this.isexist[val];
	}
	
	private int getFreq(int id) {
		if (id < 0) id = -id;
		return this.negcount[id] + this.poscount[id];
	}
	
	
	public void updatePositive(int v, int inc) {
		this.poscount[v] += inc;
	}
	
	public void updateNegative(int v, int inc) {
		this.negcount[v] += inc;
	}
	
	@Override
	public boolean hasQuantifier(int v) {
		if (v < 0) v = -v;
		return this.quantifier.contains(new Pair<Integer, Quantifier>(order[v], new Quantifier(isMax(v), v)));
	}
	
	@Override
	public void insert(Quantifier q, boolean normalized) {
		this.quantifiercount++;
		if (normalized) {
			if (!this.quantifier.contains(new Pair<Integer, Quantifier>(order[q.getVal()], q))) {
				if (!isMax(q.getVal())) {
					this.unicount++;
				}
			}
			this.quantifier.add(new Pair<Integer, Quantifier>(order[q.getVal()], q));
		} else {
			isexist[q.getVal()] = q.isMax();
			if (this.quantifier.isEmpty()) {
				if (!q.isMax()) {
					order[q.getVal()] = 1;
				} else {
					order[q.getVal()] = 0;
				}
			} else {
				Pair<Integer, Quantifier> pre = this.quantifier.last();
				if (pre.getSecond().isMax() != q.isMax()) {
					order[q.getVal()] = pre.getFirst() + 1;
				} else {
					order[q.getVal()] = pre.getFirst();
				}
			}
			this.quantifier.add(new Pair<Integer, Quantifier>(order[q.getVal()], q));
			super.quantifiers[q.getVal()] = q;
		}
	}
	
	@Override
	public void prepend(Quantifier q) {
		isexist[q.getVal()] = true;
		order[q.getVal()] = 0;
		this.quantifier.add(new Pair<Integer, Quantifier>(order[q.getVal()], q));
		super.quantifiers[q.getVal()] = q;
	}
	
	@Override
	public Quantifier peek() {
		boolean type = this.quantifier.first().getSecond().isMax();
		return peek(1, type).get(0);
	}

	@Override
	public int maxSameQuantifier(boolean type) {
		int count = 0;
		Iterator <Pair<Integer,Quantifier>> it = quantifier.iterator();
		while (count < 20 && it.hasNext()) {
			if (it.next().getSecond().isMax() != type) break;
			count++;
		}
		return count;
	}

	@Override
	public List<Quantifier> peek(int count, boolean type) {
		ArrayList<Pair<Integer, Quantifier>> mp = new ArrayList<>();
		Iterator<Pair<Integer, Quantifier>> it = quantifier.iterator();
		while (it.hasNext()) {
			Quantifier q = it.next().getSecond();
			if (q.isMax() == type) {
				mp.add(new Pair<Integer, Quantifier>(this.getFreq(q.getVal()), q));
			} else {
				break;
			}
		}
		
		Collections.sort(mp);
		count = Math.max(Math.min(count, 20), 1);
		List<Quantifier> ret = new ArrayList<Quantifier>();
		int i = 0, j = mp.size() - 1;
		while (i < count && j >= 0) {
			ret.add(mp.get(j).getSecond());
			i++;
			j--;
		}
		
		return ret;
	}
	
	@Override
	public boolean istopMax() {
		if (this.quantifier.isEmpty()) {
			System.err.println("cannot call this method when there's no quantifier");
			System.exit(1);
		}
		return this.quantifier.first().second.isMax();
	}
	
	@Override
	public int size() {
		return this.quantifier.size();
	}
 	
	@Override
	public void dropQuantifier() {
		int v = this.quantifier.first().getSecond().getVal();
		this.dropQuantifier(v);
	}

	@Override
	public void dropQuantifier(int v) {
		if (v < 0) v = -v;
		if (this.hasQuantifier(v)) {
			if (!isMax(v)) {
				this.unicount--; 
			}
			this.quantifiercount--;
			quantifier.remove(new Pair<>(order[v], super.quantifiers[v]));
		}
	}
	
	protected String toString(TreeMap<Integer, Integer> mp) {
		StringBuilder ret = new StringBuilder();
		int i = 0;
		boolean ismax = true;
		TreeSet<Integer> st = new TreeSet<>();
		ArrayList<ArrayList<Integer>> list = new ArrayList<>();
		ArrayList<Character> front = new ArrayList<>();
		ArrayList<Integer> curr = new ArrayList<>();
		for (Pair<Integer, Quantifier> p : this.quantifier) {
			if (i == 0 || ismax != p.second.isMax()) {
				if (!curr.isEmpty()) {
					list.add(curr);
					front.add(ismax ? 'e' : 'a');
				}
				curr = new ArrayList<>();
			}
			curr.add(p.second.getVal());
			st.add(p.second.getVal());
			ismax = p.second.isMax();
			++i;
		}
		
		int j = 1;
		for (Integer v : st) {
			mp.put(v, j++);
		}
		
		if (!curr.isEmpty()) {
			list.add(curr);
			front.add(ismax ? 'e' : 'a');
		}
		
		for (i = 0 ; i < list.size(); ++i) {
			ret.append(front.get(i));
			ret.append(' ');
			for (Integer v : list.get(i)) {
				ret.append(mp.get(v));
				ret.append(' ');
			}
			ret.append("0\n");
		}
		return ret.toString();
	}
}