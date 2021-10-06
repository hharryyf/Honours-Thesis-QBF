package qbfsolver;

import qbfexpression.AdjacencyListFormulaWithReason;

public class PNSNodeWithReasonTrivial extends PNSNodeWithReason {
	private boolean canexpand = true;
	public PNSNodeWithReasonTrivial(AdjacencyListFormulaWithReason f, int depth) {
		super(f, depth);
	}
	
	public PNSNodeWithReasonTrivial(AdjacencyListFormulaWithReason f, int depth, boolean dummy) {
		super(f, depth);
		this.reason = f.checkTrivial();
		if (this.reason != null) {
			this.dn = 0;
			this.pn = PNSNode.inf;
		}
	}
	
	public void expansion(AdjacencyListFormulaWithReason f) {
		if (f.evaluate() != -1) {
			System.err.println("bad!, invalid expansion");
			System.exit(0);
		}
		
		if (!canexpand) {
			this.canexpand = true;
			return;
		}
		// left split
		f.set(this.splitnode.getVal());
		f.dropquantifier(this.splitnode.getVal());
		f.simplify();
		f.commit();
		PNSNodeWithReason L = new PNSNodeWithReasonTrivial(f, this.depth + 1);
		L.parent = this;
		this.left = L;
		f.undo(this.left.reason);
		// right split
		f.set(-this.splitnode.getVal());
		f.dropquantifier(this.splitnode.getVal());
		f.simplify();
		f.commit();
		PNSNodeWithReason R = new PNSNodeWithReasonTrivial(f, this.depth + 1);
		R.parent = this;
		this.right = R;
		f.undo(this.right.reason);		
	}
	
	private boolean checkTrivial(AdjacencyListFormulaWithReason f, int idx) {
		if (this.depth > 15) return false;
		boolean ret = false;
		// check the trivial truth
		if (idx == 1) {
			if (this.left.visited != -1) {
				this.left.visited++;
				if (this.left.visited >= ResultGenerator.triviallimit) {
					f.set(this.splitnode.getVal());
					f.dropquantifier(this.splitnode.getVal());
					f.simplify();
					f.commit();
					PNSNodeWithReason L = new PNSNodeWithReasonTrivial(f, this.depth + 1, true);
					if (L.isSolved()) {
						L.parent = this;
						this.left = L;
						this.left.valid = true;
						this.canexpand = false;
						ret = true;
					}
					f.undo(this.left.reason);
					this.left.visited = -1;
				}
			}
		} else {
			if (this.right.visited != -1) {
				this.right.visited++;
				if (this.right.visited >= ResultGenerator.triviallimit) {
					f.set(-this.splitnode.getVal());
					f.dropquantifier(this.splitnode.getVal());
					f.simplify();
					f.commit();
					PNSNodeWithReason R = new PNSNodeWithReasonTrivial(f, this.depth + 1, true);
					if (R.isSolved()) {
						R.parent = this;
						this.right = R;
						this.canexpand = false;
						this.right.valid = true;
						ret = true;
					}
					f.undo(this.right.reason);		
					this.right.visited = -1;
				}
			}
		}		
		
		return ret;
	}
	
	public PNSNodeWithReason MPN(AdjacencyListFormulaWithReason f) {
		if (this.isTerminal()) return null;
		PNSNodeWithReason ret = null;
		boolean debug = ResultGenerator.getCommandLine().getDebug();
		int idx = 0;
		if (ret == null && !this.left.isSolved()) {
			ret = this.left;
			idx = 1;
		}
		
		if (debug) {
			System.out.println(this.splitnode.isMax() ? "exist " : " universe");
		}
		
		if ((ret == null && !this.right.isSolved()) 
			|| (ret != null && ret.dpn() > this.right.dpn() && !this.right.isSolved())) {
			idx = -1;
			ret = this.right;
		}
		
		if (idx == 0) {
			System.err.println("no MPN!");
			System.exit(1);
		}
		
		if (checkTrivial(f, idx)) {
			return null;
		}
		
		f.set(idx * this.splitnode.getVal());
		f.simplify();
		f.commit();
		return ret;
	}
}
