package qbfefficient;

import java.io.FileNotFoundException;
import java.util.Stack;

import qbfsolver.Result;
import qbfsolver.ResultGenerator;

public class QDeepPNS {
	protected static String lm = "Q_DEEP_PNS_SOLVE";
	private int pndnlevel = -1;
	int deeppnsbj(TwoWatchedLiteralFormula f) {
		QDeepPNSBJNode root = new QDeepPNSBJNode(f, 1), curr = root;
		int i = 0;
		long tolvisited = 0;
		Stack<TwoWatchedLiteralFormula> stk = new Stack<TwoWatchedLiteralFormula>();
		final long start = System.currentTimeMillis();
		boolean timeout = false;
		while (ResultGenerator.getInstance().getLiveNode() <= TwoWatchedLiteralFormula.max_node_in_memory * 2 
				&& i <= 4 * TwoWatchedLiteralFormula.max_node_in_memory 
				&& !root.isSolved()) {
			if (i % 1000 == 0) {
				MyLog.log(lm, pndnlevel, "Iteration #" + i + " pn = " + root.getPn() + " dn= " + root.getDn());
			}
			
			if (i % 5000 == 0) ResultGenerator.getCommandLine().setR();
			
			if (stk.empty()) {
				stk.push(f);
			}
					
			TwoWatchedLiteralFormula fp = stk.peek();
			if (curr == null) {
				curr = root;
			}
			
			QDeepPNSBJNode it;
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
				if (curr == root) break;
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
			Result rr = ResultGenerator.getInstance();
			rr.setIteration(1 + rr.getIteration());
			if (System.currentTimeMillis() - start > TwoWatchedLiteralFormula.time_limit * 1000) {
				timeout = true;
				break;
			}
		}
		MyLog.log(lm, pndnlevel, "#Iteration " + i + " pn = " + root.getPn() + " dn= " + root.getDn());
		MyLog.log(lm, 1, "#Visited: " + tolvisited);
		if (root.isWin()) {
			System.out.println("SAT");
			return 0;
		} else if (root.isLost()) {
			System.out.println("UNSAT");
			return 0;
		} 
		System.out.println("UNSOLVED");
		
		if (timeout) return -1;
		
		return 1;
	}
	
	int deeppnsqcdcl(TwoWatchedLiteralFormula f) {
		QDeepPNSLearnNode root = new QDeepPNSLearnNode(f, 1), curr = root;
		int i = 0;
		long tolvisited = 0;
		// TwoWatchedLiteralFormula.max_node_in_memory = 10000;
		Stack<TwoWatchedLiteralFormula> stk = new Stack<TwoWatchedLiteralFormula>();
		final long start = System.currentTimeMillis();
		boolean timeout = false;
		while (ResultGenerator.getInstance().getLiveNode() <= TwoWatchedLiteralFormula.max_node_in_memory * 2 
				&& i <= 4 * TwoWatchedLiteralFormula.max_node_in_memory 
				&& !root.isSolved()) {
			/*
			if (i > 22000) TwoWatchedLiteralFormula.maxLevel = 2;
			else {
				TwoWatchedLiteralFormula.maxLevel = 0;
			}
			
			if (i > 22050) return -1;
			*/
			if (i % 1000 == 0) {
				MyLog.log(lm, pndnlevel, "Iteration #" + i + " pn = " + root.getPn() + " dn= " + root.getDn());
			}
			
			if (i % 5000 == 0) ResultGenerator.getCommandLine().setR();
			
			if (stk.empty()) {
				stk.push(f);
			}
					
			TwoWatchedLiteralFormula fp = stk.peek();
			if (curr == null) {
				curr = root;
			}
			
			QDeepPNSLearnNode it;
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
				curr.backpropagation(fp);
				MyLog.log(lm, 2, curr, root);
				if (curr != root && curr.getParent() == null) {
					MyLog.log(lm, 0, "Tree is disconnected");
				} else {
					MyLog.log(lm, 2, curr.getParent());
				}
				if (((PNSLearnReason)GlobalReason.GetReason()).status == PNSLearnReason.Status.unknown && pn == curr.getPn() && dn == curr.getDn() && !curr.isSolved()) break;
				if (curr == root) {
					((PNSLearnReason)GlobalReason.GetReason()).status = PNSLearnReason.Status.unknown;
					break;
				}
				if (curr != root) {
					if (!stk.isEmpty()) {
						stk.peek().undo(GlobalReason.GetReason());
					}
					curr = curr.getParent();
				}
				stk.pop();
				tolvisited++;
			}
			
			if (curr == root) f.simplify();
			i++;
			Result rr = ResultGenerator.getInstance();
			rr.setIteration(1 + rr.getIteration());
			if (System.currentTimeMillis() - start > TwoWatchedLiteralFormula.time_limit * 1000) {
				timeout = true;
				break;
			}
		}
		MyLog.log(lm, pndnlevel, "#Iteration " + i + " pn = " + root.getPn() + " dn= " + root.getDn());
		MyLog.log(lm, 1, "#Visited: " + tolvisited);
		if (root.isWin()) {
			System.out.println("SAT");
			return 0;
		} else if (root.isLost()) {
			System.out.println("UNSAT");
			return 0;
		} 
		System.out.println("UNSOLVED");
		
		if (timeout) return -1;
		
		return 1;
	}
	
	public static void main(String args[]) throws FileNotFoundException {
		TwoWatchedLiteralConstructor reader = new TwoWatchedLiteralConstructor();
		TwoWatchedLiteralFormula ret = reader.construct();
		MyLog.log(lm, 1, "#################### Timer Start ##################");
		final long start = System.currentTimeMillis();
		QDeepPNS solver = new QDeepPNS();
		if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PBJ) {
			int res = solver.deeppnsbj(ret);
			final long end = System.currentTimeMillis();
			long cnt = TwoWatchedLiteralFormula.clause_iter, cnt2 = TwoWatchedLiteralFormula.setcount;
			MyLog.log(lm, 1, "#branching= " + ResultGenerator.getInstance().getIteration() + " #ass= " 
		              + cnt2 + " #clause iterate= " + cnt);
			MyLog.log(lm, 1, "#bcp= ", TwoWatchedLiteralFormula.bcpcount, "#ple= ", TwoWatchedLiteralFormula.plecount);
			MyLog.log(lm, 1, "nclause iterated per ass= " + (1.0 * cnt / (cnt2 + 1))); 
			MyLog.log(lm, 1, "Existential Pruning= ", TwoWatchedLiteralFormula.prunE, " Universal Pruning: ", TwoWatchedLiteralFormula.prunU, "number of resolutions", TwoWatchedLiteralFormula.rescount);
			MyLog.log(lm, 1, "total nodes", ResultGenerator.getInstance().getNode(), "total SAT nodes: ", TwoWatchedLiteralFormula.truecount, " total UNSAT nodes: ", 
					TwoWatchedLiteralFormula.falsecount, "total SAT terminal nodes: ", TwoWatchedLiteralFormula.trueterminal, "total UNSAT terminal nodes: ", TwoWatchedLiteralFormula.falseterminal);
			MyLog.log(lm, 1, "total time " + (1.0 * (end-start) / 1000));
			if (res == 0) {
				MyLog.log(lm, 1, "#################### EXIT SUCCESS ##################");
			} else if (res == 1) {
				MyLog.log(lm, 1, "#################### OUT OF MEMORY ##################");
			} else {
				MyLog.log(lm, 1, "#################### TIME OUT ##################");
			}
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PL) {
			int res = solver.deeppnsqcdcl(ret);
			final long end = System.currentTimeMillis();
			long cnt = TwoWatchedLiteralFormula.clause_iter, cnt2 = TwoWatchedLiteralFormula.setcount;
			MyLog.log(lm, 1, "#branching= " + ResultGenerator.getInstance().getIteration() + " #ass= " 
		              + cnt2 + " #clause iterate= " + cnt);
			MyLog.log(lm, 1, "#bcp= ", TwoWatchedLiteralFormula.bcpcount, "#ple= ", TwoWatchedLiteralFormula.plecount);
			MyLog.log(lm, 1, "nclause iterated per ass= " + (1.0 * cnt / (cnt2 + 1))); 
			MyLog.log(lm, 1, "Existential Pruning= ", TwoWatchedLiteralFormula.prunE, " Universal Pruning: ", TwoWatchedLiteralFormula.prunU, "number of resolutions", TwoWatchedLiteralFormula.rescount);
			MyLog.log(lm, 1, "total nodes", ResultGenerator.getInstance().getNode(), "total SAT nodes: ", TwoWatchedLiteralFormula.truecount, " total UNSAT nodes: ", 
					TwoWatchedLiteralFormula.falsecount, "total SAT terminal nodes: ", TwoWatchedLiteralFormula.trueterminal, "total UNSAT terminal nodes: ", TwoWatchedLiteralFormula.falseterminal);
			MyLog.log(lm, 1, "#learned clause= ", ret.tolLearnClause(), " #learned cube= ", ret.tolLearnCube());
			MyLog.log(lm, 1, "total time " + (1.0 * (end-start) / 1000));
			if (res == 0) {
				MyLog.log(lm, 1, "#################### EXIT SUCCESS ##################");
			} else if (res == 1) {
				MyLog.log(lm, 1, "#################### OUT OF MEMORY ##################");
			} else {
				MyLog.log(lm, 1, "#################### TIME OUT ##################");
			}
		} else {
			MyLog.log(lm, 0, "Please select the correct solver");
		}
	}
}
