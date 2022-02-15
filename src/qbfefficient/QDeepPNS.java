package qbfefficient;

import java.io.FileNotFoundException;
import java.util.Stack;

import qbfsolver.ResultGenerator;

public class QDeepPNS {
	protected static String lm = "Q_DEEP_PNS_SOLVE";
	private int maxT = 2000000;
	boolean deeppnsbj(TwoWatchedLiteralFormula f) {
		QDeepPNSNode root = new QDeepPNSNode(f, 1), curr = root;
		int i = 0;
		long tolvisited = 0;
		Stack<TwoWatchedLiteralFormula> stk = new Stack<TwoWatchedLiteralFormula>();
		while (i <= this.maxT && !root.isSolved()) {
			if (i % 1000 == 0) {
				MyLog.log(lm, 1, "Iteration #" + i + " pn = " + root.getPn() + " dn= " + root.getDn());
			}
					
			if (stk.empty()) {
				stk.push(f);
			}
					
			TwoWatchedLiteralFormula fp = stk.peek();
			if (curr == null) {
				curr = root;
			}
			
			QDeepPNSNode it;
			while (true) {
				it = curr.MPN(fp);
				if (it == null) break;
				stk.push(fp);
				curr = it;
				tolvisited++;
			}
						
			curr.expansion(fp);
			while (curr != null) {
				int pn = curr.getPn(), dn = curr.getDn();
				boolean firsttime = curr.backpropagation(fp);
				if (pn == curr.getPn() && dn == curr.getDn()) break;
				if (curr != root) {
					if (!stk.isEmpty()) {
						if (!firsttime) {
							stk.peek().undo(null);
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
		MyLog.log(lm, 1, "Iteration " + i + " pn = " + root.getPn() + " dn= " + root.getDn());
		MyLog.log(lm, 1, "Tolvisited = " + tolvisited);
		if (root.isWin()) {
			System.out.println("SAT");
			return true;
		} else if (root.isLost()) {
			System.out.println("UNSAT");
			return true;
		} 
		System.out.println("UNSOLVED");
		return false;
	}
	
	public static void main(String args[]) throws FileNotFoundException {
		TwoWatchedLiteralConstructor reader = new TwoWatchedLiteralConstructor();
		TwoWatchedLiteralFormula ret = reader.construct();
		MyLog.log(lm, 1, "#################### Timer Start ##################");
		final long start = System.currentTimeMillis();
		QDeepPNS solver = new QDeepPNS();
		if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PBJ) {
			boolean res = solver.deeppnsbj(ret);
			final long end = System.currentTimeMillis();
			long cnt = TwoWatchedLiteralFormula.clause_iter, cnt2 = TwoWatchedLiteralFormula.setcount;
			MyLog.log(lm, 1, "#branching= " + ResultGenerator.getInstance().getIteration() + " #ass= " 
		              + cnt2 + " #clause iterate= " + cnt);
			MyLog.log(lm, 1, "nclause iterated per ass= " + (1.0 * cnt / (cnt2 + 1))); 
			MyLog.log(lm, 1, "total time " + (1.0 * (end-start) / 1000));
			if (res) {
				MyLog.log(lm, 1, "#################### EXIT SUCCESS ##################");
			} else {
				MyLog.log(lm, 1, "#################### OUT OF MEMORY ##################");
			}
		}
	}
}
