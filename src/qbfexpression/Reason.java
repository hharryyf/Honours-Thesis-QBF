package qbfexpression;

import java.util.HashSet;
import java.util.Set;

public class Reason implements Comparable<Reason> {
	public boolean satisfied;
	public Set<Integer> literals;
	public Reason() {
		this.literals = new HashSet<Integer>();
	}
	
	public boolean contains(int v) {
		return literals.contains(v) || literals.contains(-v);
	}
	
	public void resolve(Reason other, int v) {
		for (Integer it : other.literals) {
			literals.add(it);
		}
		literals.remove(v);
		literals.remove(-v);
	}

	@Override
	public int compareTo(Reason o) {
		int v = literals.size() - o.literals.size();
		if (v < 0) return -1;
		if (v == 0) return 0;
		return 1;
	}
}
