package qbfsolver;

import java.util.Stack;

import qbfexpression.AdjacencyListFormulaWithReason;
import qbfexpression.CnfExpression;

public class DeepPNSWithReason implements Solver {

	private int maxT = 2000000;
	public DeepPNSWithReason() {
		
	}
	
	public DeepPNSWithReason(int T) {
		this.maxT = T;
	}
	
	@Override
	public boolean solve(CnfExpression formula) {
		// System.out.println(f);
		if (formula.getClass() != AdjacencyListFormulaWithReason.class) {
			System.err.println("invalid call to with reason solver");
			System.exit(1);
		}
		boolean debug = ResultGenerator.getCommandLine().getDebug();
		AdjacencyListFormulaWithReason f = (AdjacencyListFormulaWithReason) formula;
		PNSNodeWithReason root = new PNSNodeWithReason(f, 1), curr = root;
		int i = 0;
		long tolvisited = 0;
		Stack<AdjacencyListFormulaWithReason> stk = new Stack<AdjacencyListFormulaWithReason>();
		while (i <= this.maxT && !root.isSolved()) {
			if (i % 1000 == 0) {
				System.out.println("Iteration #" + i + " pn = " + root.getPn() + " dn= " + root.getDn());
			}
					
			if (stk.empty()) {
				stk.push(f);
			}
					
			AdjacencyListFormulaWithReason fp = stk.peek();
			if (curr == null) {
				curr = root;
			}
			
			PNSNodeWithReason it;
			if (debug) {
				System.out.println("enter MPN");
			}
			while (true) {
				it = curr.MPN(fp);
				if (it == null) break;
				stk.push(fp);
				curr = it;
				tolvisited++;
			}
			
			if (debug) {
				System.out.println("expand");
			}
			
			curr.expansion(fp);
			while (curr != null) {
				int pn = curr.getPn(), dn = curr.getDn();
				boolean firsttime = curr.backpropagation();
				if (pn == curr.getPn() && dn == curr.getDn()) break;
				if (curr != root) {
					if (!stk.isEmpty()) {
						if (!firsttime) {
							stk.peek().undo();
						} else {
							stk.peek().undo(curr.getReason());
						}
					}
					curr = curr.getParent();
				}
				stk.pop();
				tolvisited++;
			}
					
			i++;
		}
		Result res = ResultGenerator.getInstance();
		System.out.println("Iteration " + i + " pn = " + root.getPn() + " dn= " + root.getDn());
		System.out.println("Tolvisited = " + tolvisited);
		res.setIteration(i);
		if (root.isWin()) {
			res.setTruth(true);
			return true;
		}
		
		if (root.isLost()) {
			res.setTruth(false);
			return false;
		}
		
		res.setIteration(maxT + 1);
		return false;
	}
}
