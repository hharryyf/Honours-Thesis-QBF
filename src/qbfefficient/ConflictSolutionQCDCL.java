package qbfefficient;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import utilstructure.Pair;

public class ConflictSolutionQCDCL extends ConflictSolution {

	private static String lm = new String("QCDCL_LN");
	Set<Integer> literal;
	protected boolean opencount = false;
	protected TreeSet<Pair<Integer, Integer>> depth;
	public ConflictSolutionQCDCL(boolean sat) {
		this.satisfied = sat;
		this.literal = new HashSet<>();
		this.depth = new TreeSet<>();
		this.opencount = false;
	}
	
	public List<Integer> allLiteral() {
		List<Integer> ret = new ArrayList<>();
		for (Pair<Integer, Integer> p : depth) {
			ret.add(p.second);
		}
		return ret;
	}
	
	@Override
	public int compareTo(ConflictSolution o) {
		Integer it = new Integer(this.size());
		Integer it2 = new Integer(o.size());
		return it.compareTo(it2);
	}

	@Override
	public void addLiteral(EfficientQBFFormula f, TwoWatchedLiteralClause c) {
		for (Integer v : c.existential) {
			depth.add(new Pair<>(f.depth(v), v));
			if (!f.isassigned(v)) this.opencount = true;
			literal.add(v);
		}
		
		for (Integer v : c.universal) {
			depth.add(new Pair<>(f.depth(v), v));
			if (!f.isassigned(v)) this.opencount = true;
			literal.add(v);
		}
	}

	@Override
	public void addAssignment(EfficientQBFFormula f, List<Integer> c) {
		// assume c is in T-minimal form
		for (Integer v : c) {
			depth.add(new Pair<>(f.depth(v), v));
			if (!f.isassigned(v)) this.opencount = true;
			literal.add(v);
		}
	}
	
	
	private ConflictSolutionQCDCL qresolution(EfficientQBFFormula f, ConflictSolutionQCDCL w1, ConflictSolutionQCDCL w2, int v) {
		ConflictSolutionQCDCL ret = new ConflictSolutionQCDCL(w1.satisfied);
		for (Integer u : w1.literal) {
			ret.literal.add(u);
			ret.depth.add(new Pair<>(f.depth(u), u));
		}
		for (Integer u : w2.literal) {
			ret.literal.add(u);
			ret.depth.add(new Pair<>(f.depth(u), u));
		}
		
		ret.literal.remove(-v);
		ret.literal.remove(v);
		ret.depth.remove(new Pair<>(f.depth(v), v));
		ret.depth.remove(new Pair<>(f.depth(v), -v));
		while (!ret.depth.isEmpty()) {
			Pair<Integer, Integer> d = ret.depth.last();
			if (this.satisfied == f.isMax(d.second)) {
				ret.literal.remove(d.second);
				ret.depth.remove(d);
			} else {
				break;
			}
		}
		
		this.opencount = false;
		for (Integer u : ret.literal) {
			if (!f.isassigned(u)) this.opencount = true;
		}
		
		//System.out.println("q resolution " + w1 + " " + w2 + " get " + ret + " " + ret.depth);
		return ret;
	}
	
	private ConflictSolutionQCDCL rec_c_resolve(EfficientQBFFormula f, ConflictSolutionQCDCL w1, ConflictSolutionQCDCL w2, int v) {
		boolean ok = true;
		for (Integer u : w2.literal) {
			if (Math.abs(u) != Math.abs(v) && w1.contains(-u)) {
				ok = false;
				break;
			}
		}
		
		if (ok) return qresolution(f, w1, w2, v);
		Iterator<Pair<Integer, Integer>> iter = w1.depth.descendingIterator();
		ConflictSolutionQCDCL w = new ConflictSolutionQCDCL(w1.satisfied);
		int l = 0;
		boolean find = false;
		while (iter.hasNext()) {
			Pair<Integer, Integer> p = iter.next();
			TwoWatchedLiteralClause c = f.unitId(-p.second);
			l = p.second;
			if (c != null) {
				w.addLiteral(f, c);
				find = true;
				break;
			}
		}
		
		if (!find) {
			MyLog.log(lm, 0, "cannot find the unit, something's wrong");
		}
		
		w = qresolution(f, w1, w, l);
		return rec_c_resolve(f, w, w2, v);
	}
	
	@Override
	public void resolve(ConflictSolution other, int v, EfficientQBFFormula f) {
		if (other.getClass() != ConflictSolutionQCDCL.class) MyLog.log(lm, 0, "resolve different clase");
		if (other.satisfied != this.satisfied) MyLog.log(lm, 0, "resolve different type");
		MyLog.log(lm, 2, "resolve: ",this, " ", this.satisfied, " and ");
		ConflictSolutionQCDCL ret = rec_c_resolve(f, this, (ConflictSolutionQCDCL) other, v);
		this.literal = ret.literal;
		this.depth = ret.depth;
		this.opencount = ret.opencount;
		MyLog.log(lm, 2, other,  " get ", this, " ", other.satisfied);
		
	}

	@Override
	public int size() {
		return this.literal.size();
	}

	@Override
	public boolean contains(int v) {
		return this.literal.contains(v);
	}

	@Override
	public void drop(EfficientQBFFormula f, int v) {
		if (f == null) MyLog.log(lm, 0, "formula cannot be null");
		depth.remove(new Pair<>(f.depth(v), v));
		literal.remove(v);
	}
	
	// v is the current assigned left-right branch
	public boolean isUIP(EfficientQBFFormula f, int v) {
		if (this.opencount) return false;
		if (f.isMax(v) && this.literal.contains(-v) && !f.isassigned(-v)) return true;
		if (!f.isMax(v) && this.literal.contains(v) && !f.isassigned(v)) return true;
		return false;
	}
	
	public String toString() {
		return this.literal.toString();
	}

}
