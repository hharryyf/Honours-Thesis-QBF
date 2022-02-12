package qbfefficient;
import java.io.FileNotFoundException;
import java.util.Random;

import qbfexpression.Quantifier;
import qbfsolver.Result;
import qbfsolver.ResultGenerator;
import utilstructure.Pair;

public class QDPLL {
	protected static String lm = new String("QDPLL");
	public Pair<ConflictSolution, Boolean> cdclsbj(TwoWatchedLiteralFormula f, int d) {
		Result rr = ResultGenerator.getInstance();
		rr.setIteration(1 + rr.getIteration());
		if (f == null) return null;
		int ret = f.evaluate();
		Random rd = new Random();
		int idx = rd.nextInt(2) == 1 ? 1 : -1;
		if (!TwoWatchedLiteralFormula.rand) idx = 1;
		if (ret == 0) {
			return new Pair<>(f.getReason(), false);
		}
		if (ret == 1) return new Pair<>(f.getReason(), true);
		Quantifier q = f.peek();
		if (q.isMax()) {
			f.set(q.getVal() * idx);
			f.simplify();
			Pair<ConflictSolution, Boolean> res = cdclsbj(f, d + 1);
			f.undo(res.first);
			if (res.second || !res.first.contains(-q.getVal() * idx)) {
				if (!res.second && !res.first.contains(-q.getVal() * idx)) {
			    	System.out.println("p-E " + q.getVal() * idx  + " d=" + d);
			    }
				return res;
			}
			f.set(-q.getVal() * idx);
			f.simplify();
			Pair<ConflictSolution, Boolean> other = cdclsbj(f, d + 1);
			f.undo(other.first);
			if (!other.second && other.first.contains(q.getVal() * idx)) {
			    other.first.resolve(res.first, q.getVal(), f);
			    if (TwoWatchedLiteralFormula.depend && TwoWatchedLiteralFormula.debug) {
			    	System.out.println("resolve E num= " + q.getVal());
			    }
			}
			return other;
		}
		
		f.set(q.getVal() * idx);
		//System.out.println("enter simp " + q.getVal() + " " + d);
		f.simplify();
		//System.out.println("exit simp " + q.getVal() + " " + d);
		Pair<ConflictSolution, Boolean> res = cdclsbj(f, d + 1);
		f.undo(res.first);
		if (!res.second || !res.first.contains(q.getVal() * idx)) {
		    if (res.second && !res.first.contains(q.getVal() * idx)) {
		    	System.out.println("p-U " + q.getVal() * idx + " d=" + d);
		    }
			return res;
		}
		f.set(-q.getVal() * idx);
		f.simplify();
		Pair<ConflictSolution, Boolean> other = cdclsbj(f, d + 1);
		f.undo(other.first);
		if (other.second && other.first.contains(-q.getVal() * idx)) {
		    other.first.resolve(res.first, q.getVal() * idx, f);
		    if (TwoWatchedLiteralFormula.depend && TwoWatchedLiteralFormula.debug) {
		    	System.out.println("resolve U num= " + q.getVal() * idx);
		    }
		}
		return other;
	}
	
	public Pair<ConflictSolution, Boolean> backjumping(TwoWatchedLiteralFormula f, int d) {
		Result rr = ResultGenerator.getInstance();
		rr.setIteration(1 + rr.getIteration());
		if (f == null) return null;
		int ret = f.evaluate();
		if (ret == 0) {
			return new Pair<>(f.getReason(), false);
		}
		if (ret == 1) return new Pair<>(f.getReason(), true);
		Quantifier q = f.peek();
		if (q.isMax()) {
			f.set(q.getVal());
			f.simplify();
			Pair<ConflictSolution, Boolean> res = backjumping(f, d + 1);
			f.undo(res.first);
			if (res.second || !res.first.contains(q.getVal())) {
				if (!res.second && !res.first.contains(q.getVal())) {
			    	System.out.println("p-E " + q.getVal()  + " d=" + d);
			    }
				res.first.drop(null, q.getVal());
				return res;
			}
			f.set(-q.getVal());
			f.simplify();
			Pair<ConflictSolution, Boolean> other = backjumping(f, d + 1);
			f.undo(other.first);
			if (!other.second && other.first.contains(-q.getVal())) {
			    other.first.resolve(res.first, q.getVal(), f);
			}
			return other;
		}
		
		f.set(q.getVal());
		f.simplify();
		Pair<ConflictSolution, Boolean> res = backjumping(f, d + 1);
		f.undo(res.first);
		if (!res.second || !res.first.contains(q.getVal())) {
		    if (res.second && !res.first.contains(q.getVal())) {
		    	System.out.println("p-U " + q.getVal() + " d=" + d);
		    }
			res.first.drop(null, q.getVal());
			return res;
		}
		f.set(-q.getVal());
		f.simplify();
		Pair<ConflictSolution, Boolean> other = backjumping(f, d + 1);
		f.undo(other.first);
		if (other.second && other.first.contains(-q.getVal())) {
		    other.first.resolve(res.first, q.getVal(), f);
		}
		return other;
	}
	
	public boolean baseline(TwoWatchedLiteralFormula f) {
		Result rr = ResultGenerator.getInstance();
		rr.setIteration(1 + rr.getIteration());
		if (f == null) return true;
		int ret = f.evaluate();
		if (ret == 0) {
			f.getReason();
			return false;
		}
		if (ret == 1) return true;
		Quantifier q = f.peek();
		if (q.isMax()) {
			f.set(q.getVal());
			f.simplify();
			boolean res = baseline(f);
			f.undo(null);
			if (res) {
				return true;
			}
			f.set(-q.getVal());
			f.simplify();
			res = baseline(f);
			f.undo(null);
			return res;
		}
		
		f.set(q.getVal());
		f.simplify();
		boolean res = baseline(f);
		f.undo(null);
		if (!res) {
			return false;
		}
		f.set(-q.getVal());
		f.simplify();
		res = baseline(f);
		f.undo(null);
		return res;
	}
	
	public static void main(String args[]) throws FileNotFoundException {
		final long start = System.currentTimeMillis();
		TwoWatchedLiteralConstructor reader = new TwoWatchedLiteralConstructor();
		TwoWatchedLiteralFormula ret = reader.construct();
		QDPLL solver = new QDPLL();
		boolean res = false;
		if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BT) {
			res = solver.baseline(ret);
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BJ) {
			res = solver.backjumping(ret, 0).second;
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.CDCLSBJ) {
			res = solver.cdclsbj(ret, 0).second;
		} else {
			
		}
		final long end = System.currentTimeMillis();
		long cnt = TwoWatchedLiteralFormula.clause_iter, cnt2 = TwoWatchedLiteralFormula.setcount;
		MyLog.log(lm, false, "#branching= " + ResultGenerator.getInstance().getIteration() + " #ass= " 
	              + cnt2 + " #clause iterate= " + cnt);
		MyLog.log(lm, false, "nclause iterated per ass= " + (1.0 * cnt / (cnt2 + 1))); 
	    MyLog.log(lm, false, "total time " + (1.0 * (end-start) / 1000));
		System.out.println((res ? "SAT" : "UNSAT"));
	}
}
