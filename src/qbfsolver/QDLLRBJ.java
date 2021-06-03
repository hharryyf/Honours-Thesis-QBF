package qbfsolver;

import qbfexpression.AdjacencyListFormula;
import qbfexpression.CnfExpression;
import qbfexpression.Quantifier;
import qbfexpression.Reason;
import utilstructure.Pair;

public class QDLLRBJ implements Solver {
    
	private Pair<Boolean, Reason> solvebj(AdjacencyListFormula f) {
		Result rr = ResultGenerator.getInstance();
		rr.setIteration(1 + rr.getIteration());
		if (f == null) return new Pair<Boolean, Reason>(true, null);
		if (f.getn() <= 0) return new Pair<Boolean, Reason>(true, null);
		int ret = f.evaluate();
		// if this is the "leaf" node, we put the reason to the parent
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
			if (res.first || !res.second.contains(q.getVal())) {
				if (!res.first) {
					System.out.println("pruning");
				}
				return res;
			}
			f.set(-q.getVal());
			f.dropquantifier(q.getVal());
			f.simplify();
			f.commit();
			Pair<Boolean, Reason> res2 = solvebj(f);
			f.undo(res2.second);
			if (res2.first == false) {
				res2.second.resolve(res.second, q.getVal());
			}
			return res2;
		}
		
		Quantifier q = f.peek();
		f.set(q.getVal());
		f.dropquantifier(q.getVal());
		f.simplify();
		f.commit();
		Pair<Boolean, Reason> res = solvebj(f);
		f.undo(res.second);
		if (!res.first || !res.second.contains(q.getVal())) {
			if (res.first) {
				System.out.println("pruning");
			}
			return res;
		}
		f.set(-q.getVal());
		f.dropquantifier(q.getVal());
		f.simplify();
		f.commit();
		Pair<Boolean, Reason> res2 = solvebj(f);
		f.undo(res2.second);
		if (res2.first == true) {
			res2.second.resolve(res.second, q.getVal());
		}
		return res2;
	}
	
	@Override
	public boolean solve(CnfExpression f) {
		System.out.println("enter solve");
		return solvebj((AdjacencyListFormula)f).first;
	}

}
