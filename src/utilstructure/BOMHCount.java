package utilstructure;

import java.util.Iterator;
import java.util.Map;
import java.util.TreeMap;

import qbfexpression.Quantifier;

public class BOMHCount implements Comparable<BOMHCount> {
	protected TreeMap<Integer, Integer> vc;
	private Quantifier q;
	public BOMHCount(Quantifier q) {
		this.vc = new TreeMap<>();
		this.q = q;
	}
	
	public Quantifier getQuantifier() {
		return this.q;
	}
	
	public void add(int v) {
		this.vc.put(v, this.vc.getOrDefault(v, 0) + 1);
	}
	
	@Override
	public int compareTo(BOMHCount other) {
		Iterator<Map.Entry<Integer, Integer>> it = vc.entrySet().iterator();
		Iterator<Map.Entry<Integer, Integer>> it2 = other.vc.entrySet().iterator();
		while (it.hasNext() && it2.hasNext()) {
			Map.Entry<Integer, Integer> e1 = it.next();
			Map.Entry<Integer, Integer> e2 = it2.next();
			if (e1.getKey() < e2.getKey()) return -1;
			if (e1.getKey() > e2.getKey()) return 1;
			if (e1.getValue() < e2.getValue()) return 1;
			if (e1.getValue() > e2.getValue()) return -1;
		}
		
		if (it.hasNext()) return -1;
		if (it2.hasNext()) return 1;
		return 0;
	}
	
	@Override
	public String toString() {
		return q + " " + vc;
	}
}
