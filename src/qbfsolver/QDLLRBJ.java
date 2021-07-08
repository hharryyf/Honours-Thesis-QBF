package qbfsolver;

import java.util.Random;

import qbfexpression.AdjacencyListFormulaWithReason;
import qbfexpression.CnfExpression;
import qbfexpression.Quantifier;
import qbfexpression.Reason;
import utilstructure.Pair;

public class QDLLRBJ implements Solver {
    
	private Pair<Boolean, Reason> solvebj(AdjacencyListFormulaWithReason f, int d) {
		Result rr = ResultGenerator.getInstance();
		boolean debug = ResultGenerator.getCommandLine().getDebug();
		//Random r = new Random();
		//int idx = r.nextInt(2) == 0 ? 1 : -1;
		//int idx = 1;
		
		rr.setIteration(1 + rr.getIteration());
		/*if (rr.getIteration() >= 4000001) {
			System.out.println("UNSOLVE");
			System.exit(0);
		}*/
		if (f == null) return new Pair<Boolean, Reason>(true, null);
		if (f.getn() <= 0) return new Pair<Boolean, Reason>(true, null);
		int ret = f.evaluate();
		if (ret == 0) {
			return new Pair<Boolean, Reason>(false, f.getReason());
		}
		
		if (ret == 1) {
			return new Pair<Boolean, Reason>(true, f.getReason());
		}
		
		if (ResultGenerator.variate) {
			if (d > 20) {
				ResultGenerator.bomh = false;
			} else {
				ResultGenerator.bomh = true;
			}
		}
		Quantifier q = f.peek();
		boolean type = q.isMax();
		int idx = 1;
		if (ResultGenerator.dlis) {
			idx = f.getPosfreq(q.getVal()) >= f.getNegfreq(q.getVal()) ? 1 : -1;
			if (!q.isMax()) {
				idx *= -1;
			}
		}
		if (type) {
			
			//System.out.println("splitnode= " + q.getVal());
			f.set(q.getVal() * idx);
			f.dropquantifier(q.getVal());
			f.simplify();
			f.commit();
			Pair<Boolean, Reason> res = solvebj(f, d + 1);
			// when we call undo the reason is already stored in reason[depth]
			f.undo(res.second);
			// we need to push the reason back to the parent
			// check if it is a pruning condition
			if (debug) {
				System.out.println("reasons at node " + q.getVal() + " is " + res.second.literals);
			}
			if (res.first || !res.second.contains(q.getVal())) {
				if (!res.first) {
					//if (debug) {
						System.out.print("p-E " + q.getVal());
					//}
				}
				// System.out.println(" early exit at level " + depth + " it= " + rr.getIteration());
				System.out.println(" d=" + d + " r=" + rr.getIteration());
				res.second.satisfied = res.first;
				return res;
			}
			f.set(-q.getVal() * idx);
			f.dropquantifier(q.getVal());
			f.simplify();
			f.commit();
			Pair<Boolean, Reason> res2 = solvebj(f, d + 1);
			f.undo(res2.second);
			if (res2.first == false && res2.second.contains(q.getVal())) {
				if (debug) {
					System.out.println("resolve things " + res2.second.literals + " " + res.second.literals);
				}
				res2.second.resolve(res.second, q.getVal());
				//res2.second.satisfied = false;
				if (debug) {
					System.out.println("after resolve at "+ q.getVal() + " we get " + res2.second.literals);
				}
			}
			res2.second.satisfied = res2.first;
			return res2;
		}
		//System.out.println("splitnode= " + q.getVal());
		f.set(q.getVal() * idx);
		f.dropquantifier(q.getVal());
		f.simplify();
		f.commit();
		Pair<Boolean, Reason> res = solvebj(f, d + 1);
		f.undo(res.second);
		if (debug) {
			System.out.println("reasons at node " + q.getVal() + " is " + res.second.literals);
		}
		
		if (!res.first || !res.second.contains(q.getVal())) {
			if (res.first) {
				System.out.print("p-U " + q.getVal());
			}
			res.second.satisfied = res.first;
			System.out.println(" d=" + d + " r=" + rr.getIteration());
			//System.out.println(" early exit at depth " + depth + " it= " + rr.getIteration());
			return res;
		}
		f.set(-q.getVal() * idx);
		f.dropquantifier(q.getVal());
		f.simplify();
		f.commit();
		Pair<Boolean, Reason> res2 = solvebj(f, d + 1);
		f.undo(res2.second);
		
		if (res2.first == true && res2.second.contains(q.getVal())) {
			if (debug) {
				System.out.println("resolve things " + res2.second.literals + " " + res.second.literals);
			}
			res2.second.resolve(res.second, q.getVal());	
			if (debug) {
				System.out.println("after resolve at " + q.getVal() + " we get " + res2.second.literals);
			}
		}
		res2.second.satisfied = res2.first;
		return res2;
	}
	
	@Override
	public boolean solve(CnfExpression f) {
		System.out.println("enter QDLL Backjumping solver");
		return solvebj((AdjacencyListFormulaWithReason)f, 0).first;
	}

}
