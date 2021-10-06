package qbfefficient;
import java.io.FileNotFoundException;

import qbfexpression.Quantifier;
import qbfsolver.Result;
import qbfsolver.ResultGenerator;

public class QCDCL {
	public boolean solve(TwoWatchedLiteralFormula f) {
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
			boolean res = solve(f);
			f.undo();
			if (res) {
				return true;
			}
			f.set(-q.getVal());
			f.simplify();
			res = solve(f);
			f.undo();
			return res;
		}
		
		f.set(q.getVal());
		f.simplify();
		boolean res = solve(f);
		f.undo();
		if (!res) {
			return false;
		}
		f.set(-q.getVal());
		f.simplify();
		res = solve(f);
		f.undo();
		return res;
	}
	
	public static void main(String args[]) throws FileNotFoundException {
		TwoWatchedLiteralConstructor reader = new TwoWatchedLiteralConstructor();
		TwoWatchedLiteralFormula ret = reader.construct();
		QCDCL solver = new QCDCL();
		System.out.println(solver.solve(ret) + " " + ResultGenerator.getInstance().getIteration());
	}
}
