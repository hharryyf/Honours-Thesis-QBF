package qbfefficient;

import java.util.TreeSet;

import utilstructure.Pair;

public class ConflictSolution {
	// (depth, literal)
	protected TreeSet<Pair<Integer, Integer>> literal;
	protected int opencount;
	protected boolean satisfied;
	public ConflictSolution() {
		this.literal = new TreeSet<>();
	}
	
	public void resolve(ConflictSolution other, int v, EfficientQBFFormula f) {
		if (other.satisfied != this.satisfied) MyError.abort("error: resolve a solution and conflict together");
		// TODO
	}
}
