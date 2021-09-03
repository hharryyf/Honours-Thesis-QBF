package qbfsolver;

import qbfexpression.AdjacencyListFormulaCDCL;
import qbfexpression.CnfExpression;
import qbfexpression.Quantifier;

public class QDLLR implements Solver {
	@Override
	public boolean solve(CnfExpression f) {
			Result rr = ResultGenerator.getInstance();
			rr.setIteration(1 + rr.getIteration());
			if (f == null) return true;
			if (f.getn() <= 0) return true;
			int ret = f.evaluate();
			if (ret == 0) {
				if (ResultGenerator.cdcl) {
					((AdjacencyListFormulaCDCL) f).getConflict();
				}
				return false;
			}
			if (ret == 1) return true;
			boolean type = f.peek().isMax();
			if (type) {
				Quantifier q = f.peek();
				f.set(-q.getVal());
				f.dropquantifier(q.getVal());
				f.simplify();
				f.commit();
				boolean res = solve(f);
				f.undo();
				if (res) {
					return true;
				}
				f.set(q.getVal());
				f.dropquantifier(q.getVal());
				f.simplify();
				f.commit();
				res = solve(f);
				f.undo();
				return res;
			}
			
			
			Quantifier q = f.peek();
			f.set(-q.getVal());
			f.dropquantifier(q.getVal());
			f.simplify();
			f.commit();
			boolean res = solve(f);
			f.undo();
			if (!res) {
				return false;
			}
			f.set(q.getVal());
			f.dropquantifier(q.getVal());
			f.simplify();
			f.commit();
			res = solve(f);
			f.undo();
			return res;
	}
}
