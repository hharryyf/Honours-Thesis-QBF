package utilstructure;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.TreeMap;

import qbfexpression.Quantifier;

public class BOMHVector implements Comparable<BOMHVector> {
	protected TreeMap<Integer, Integer> vc;
	private HashMap<Integer, Integer> pos;
	private HashMap<Integer, Integer> neg;
	private Quantifier q;
	public BOMHVector(Quantifier q) {
		this.vc = new TreeMap<>();
		this.pos = new HashMap<>();
		this.neg = new HashMap<>();
		this.q = q;
	}
	
	public Quantifier getQuantifier() {
		return this.q;
	}
	
	public void add(int v, boolean positive) {
		if (positive) {
			this.pos.put(v, this.pos.getOrDefault(v, 0) + 1);
		} else {
			this.neg.put(v, this.neg.getOrDefault(v, 0) + 1);
		}
	}
	
	public void normalize() {
		for (Integer it : pos.keySet()) {
			int hp = pos.get(it), hn = neg.getOrDefault(it, 0);
			vc.put(it, Math.max(hp, hn) + 2 * Math.min(hp, hn));
		}
		
		for (Integer it : neg.keySet()) {
			int hp = neg.get(it), hn = pos.getOrDefault(it, 0);
			vc.put(it, Math.max(hp, hn) + 2 * Math.min(hp, hn));
		}
	}
	
	@Override
	public int compareTo(BOMHVector other) {
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
