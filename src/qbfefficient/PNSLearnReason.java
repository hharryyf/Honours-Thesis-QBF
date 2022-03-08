package qbfefficient;

import java.util.Iterator;

import utilstructure.Pair;

public class PNSLearnReason extends ConflictSolutionQCDCL {
	private static String lm = new String("PNS_Learn_Reason");
	public enum Status {
		unknown, pending, pendingL, lock;
	}
	
	public Status status = Status.unknown;
	public PNSLearnReason(boolean sat) {
		super(sat);
	}
	
	private PNSLearnReason qresolution(EfficientQBFFormula f, PNSLearnReason w1, PNSLearnReason w2, int v) {
		PNSLearnReason ret = new PNSLearnReason(w1.satisfied);
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
	
	private PNSLearnReason rec_c_resolve(EfficientQBFFormula f, PNSLearnReason w1, PNSLearnReason w2, int v) {
		MyLog.log(lm, 2, "resolve_c_resolve", w1, w2);
		boolean ok = true;
		for (Integer u : w2.literal) {
			if (Math.abs(u) != Math.abs(v) && w1.contains(-u)) {
				ok = false;
				break;
			}
		}
		
		if (ok) return qresolution(f, w1, w2, v);
		Iterator<Pair<Integer, Integer>> iter = w1.depth.descendingIterator();
		PNSLearnReason w = new PNSLearnReason(w1.satisfied);
		int l = 0;
		boolean find = false;
		while (iter.hasNext()) {
			Pair<Integer, Integer> p = iter.next();
			TwoWatchedLiteralClause c = f.unitId(-p.second);
			l = p.second;
			if (c != null) {
				w.addLiteral(f, c);
				MyLog.log(lm, 2, "find unit in long distance resolution with depth", p.first, "unit literal", -p.second);
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
		if (other.getClass() != PNSLearnReason.class) MyLog.log(lm, 0, "resolve different clase");
		if (other.satisfied != this.satisfied) MyLog.log(lm, 0, "resolve different type");
		MyLog.log(lm, 2, "resolve: ",this, " ", this.satisfied, " and ");
		PNSLearnReason ret = rec_c_resolve(f, this, (PNSLearnReason) other, v);
		this.literal = ret.literal;
		this.depth = ret.depth;
		this.opencount = ret.opencount;
		MyLog.log(lm, 2, other,  " get ", this, " ", other.satisfied);
		
	}
}
