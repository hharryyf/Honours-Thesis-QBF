package qbfsolver;

import qbfexpression.AdjacencyListFormula;
import qbfexpression.CnfExpression;
import qbfexpression.Quantifier;
import qbfexpression.Reason;
import utilstructure.Pair;

public class QDLLRBJ implements Solver {
    
	private Pair<Boolean, Reason> solvebj(AdjacencyListFormula f) {
		Result rr = ResultGenerator.getInstance();
		boolean debug = ResultGenerator.getCommandLine().getDebug();
		rr.setIteration(1 + rr.getIteration());
		if (f == null) return new Pair<Boolean, Reason>(true, null);
		if (f.getn() <= 0) return new Pair<Boolean, Reason>(true, null);
		int ret = f.evaluate();
		if (ret == 0) {
			return new Pair<Boolean, Reason>(false, f.getReason());
		}
		
		if (ret == 1) {
			return new Pair<Boolean, Reason>(true, f.getReason());
		}
		boolean type = f.peek().isMax();
		if (type) {
			Quantifier q = f.peek();
			f.set(q.getVal());
			f.dropquantifier(q.getVal());
			f.simplify();
			f.commit();
			Pair<Boolean, Reason> res = solvebj(f);
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
						System.out.println("pruning E " + q.getVal());
					//}
				}
				
				res.second.satisfied = res.first;
				return res;
			}
			f.set(-q.getVal());
			f.dropquantifier(q.getVal());
			f.simplify();
			f.commit();
			Pair<Boolean, Reason> res2 = solvebj(f);
			f.undo(res2.second);
			if (res2.first == false) {
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
		
		Quantifier q = f.peek();
		f.set(q.getVal());
		f.dropquantifier(q.getVal());
		f.simplify();
		f.commit();
		Pair<Boolean, Reason> res = solvebj(f);
		f.undo(res.second);
		if (debug) {
			System.out.println("reasons at node " + q.getVal() + " is " + res.second.literals);
		}
		
		if (!res.first || !res.second.contains(q.getVal())) {
			if (res.first) {
				System.out.println("pruning U " + q.getVal());
			}
			res.second.satisfied = res.first;
			return res;
		}
		f.set(-q.getVal());
		f.dropquantifier(q.getVal());
		f.simplify();
		f.commit();
		Pair<Boolean, Reason> res2 = solvebj(f);
		f.undo(res2.second);
		
		if (res2.first == true) {
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
		return solvebj((AdjacencyListFormula)f).first;
	}

}
