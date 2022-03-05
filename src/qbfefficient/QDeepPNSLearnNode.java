package qbfefficient;

import java.util.ArrayList;
import java.util.List;

import qbfexpression.Quantifier;
import qbfsolver.Result;
import qbfsolver.ResultGenerator;

public class QDeepPNSLearnNode {
	protected static String lm = new String("QDeepPNSLearnNode");
	Quantifier splitnode;
	int visited = 0;
	QDeepPNSLearnNode left = null, right = null, parent = null;
	int pn, dn, depth, size;
	double deep;
	public static int inf = 120000000;
	public QDeepPNSLearnNode(TwoWatchedLiteralFormula f, int depth) {
		this.visited = 1;
		this.deep = 1.0 / depth;
		this.depth = depth;
		this.left = this.right = this.parent = null;
		Result rr = ResultGenerator.getInstance();
		rr.setNode();
		int val = f.evaluate();
		if (val == 1) {
			this.pn = 0;
			this.dn = QDeepPNSBJNode.inf;
			TwoWatchedLiteralFormula.truecount++;
		} else if (val == 0) {
			this.pn = QDeepPNSBJNode.inf;
			this.dn = 0;
			TwoWatchedLiteralFormula.falsecount++;
		} else {
			this.pn = 1;
			this.dn = 1;
			this.splitnode = f.peek();
			if (this.splitnode.isMax()) {
				this.dn = 2;
			} else {
				this.pn = 2;
			}
		}
		
		this.size = 1;
	}
	
	public QDeepPNSLearnNode getParent() {
		return this.parent;
	}
	
	public boolean isTerminal() {
		return this.left == null && this.right == null;
	}
	
	public boolean isSolved() {
		return this.pn >= QDeepPNSLearnNode.inf || this.dn >= QDeepPNSLearnNode.inf;
	}
	
	public boolean isLost() {
		return this.pn >= QDeepPNSLearnNode.inf;
	}
	
	public boolean isWin() {
		return this.dn >= QDeepPNSLearnNode.inf;
	}
	
	public int getPn() {
		return this.pn;
	}
	
	public int getDn() {
		return this.dn;
	}
	
	public int getDelta() {
		if (this.splitnode == null) return this.pn;
		if (this.splitnode.isMax()) return this.dn;
		return this.pn;
	}
	
	public int getPhi() {
		if (this.splitnode == null) return this.dn;
		if (this.splitnode.isMax()) return this.pn;
		return this.dn;
	}
	
	public double dpn() {
		double R = ResultGenerator.getCommandLine().getR();
		return (1.0 - 1.0 / this.getDelta()) * R + this.deep * (1.0 - R);
	}
	
	protected void setTrue() {
		this.pn = 0;
		this.dn = QDeepPNSLearnNode.inf;
	}
	
	protected void setFalse() {
		this.dn = 0;
		this.pn = QDeepPNSLearnNode.inf;
	}
	
	
	public void expansion(TwoWatchedLiteralFormula f) {
		if (this.isSolved() || f.evaluate() != -1) {
			return;
		}
		
		// peek a new quantifier
		if (f.isassigned(this.splitnode.getVal())) this.splitnode = f.peek();
		// left split
		f.set(this.splitnode.getVal());
		f.simplify();
		QDeepPNSLearnNode L = new QDeepPNSLearnNode(f, this.depth + 1);
		L.parent = this;
		this.left = L;
		ConflictSolution lreason = new PNSLearnReason(false), rreason = new PNSLearnReason(false);
		if (this.left.isSolved()) {
			lreason = f.getReason();
		}
		f.undo(lreason);
		// right split
		f.set(-this.splitnode.getVal());
		f.simplify();
		QDeepPNSLearnNode R = new QDeepPNSLearnNode(f, this.depth + 1);
		R.parent = this;
		this.right = R;
		if (this.right.isSolved()) {
			rreason = f.getReason();
		}
		f.undo(rreason);
		// TODO, calculate the reason for the root
		if (((PNSLearnReason) lreason).status == PNSLearnReason.Status.pending || ((PNSLearnReason) lreason).status == PNSLearnReason.Status.pendingL) {
			GlobalReason.setReason((PNSLearnReason) lreason);
		} else if (((PNSLearnReason) rreason).status == PNSLearnReason.Status.pending || ((PNSLearnReason) rreason).status == PNSLearnReason.Status.pendingL) {
			GlobalReason.setReason((PNSLearnReason) rreason);
		} else if (((PNSLearnReason) lreason).status != PNSLearnReason.Status.unknown && ((PNSLearnReason) rreason).status != PNSLearnReason.Status.unknown) {
			if (((PNSLearnReason) lreason).satisfied && ((PNSLearnReason) rreason).satisfied) {
				lreason.resolve(rreason, this.splitnode.getVal(), f);
				GlobalReason.setReason((PNSLearnReason) lreason);
				ConflictSolution r = GlobalReason.GetReason();
				((PNSLearnReason) r).status = PNSLearnReason.Status.pendingL;
			} else if (!((PNSLearnReason) lreason).satisfied && !((PNSLearnReason) rreason).satisfied) {
				lreason.resolve(rreason, this.splitnode.getVal(), f);
				GlobalReason.setReason((PNSLearnReason) lreason);
				ConflictSolution r = GlobalReason.GetReason();
				((PNSLearnReason) r).status = PNSLearnReason.Status.pendingL;
			} else if (((PNSLearnReason) lreason).satisfied && !((PNSLearnReason) rreason).satisfied) {
				if (f.isMax(this.splitnode.getVal())) {
					GlobalReason.setReason((PNSLearnReason) lreason);
				} else {
					GlobalReason.setReason((PNSLearnReason) rreason);
				}
			} else {
				if (f.isMax(this.splitnode.getVal())) {
					GlobalReason.setReason((PNSLearnReason) rreason);
				} else {
					GlobalReason.setReason((PNSLearnReason) lreason);
				}
			}
		}
	}
	
	public QDeepPNSLearnNode MPN(TwoWatchedLiteralFormula f) {
		if (this.isTerminal() || this.isSolved()) return null;
		int val = f.evaluate();
		if (val != -1) {
			if (val == 1) {
				this.pn = 0;
				this.dn = QDeepPNSBJNode.inf;
				TwoWatchedLiteralFormula.truecount++;
				GlobalReason.setReason((PNSLearnReason) f.getReason());
			} else if (val == 0) {
				this.pn = QDeepPNSBJNode.inf;
				this.dn = 0;
				TwoWatchedLiteralFormula.falsecount++;
				GlobalReason.setReason((PNSLearnReason) f.getReason());
			}
			this.left = this.right = null;
			return null;
		}
		
		int v = this.splitnode.getVal();
		boolean Lass = f.assignlit(v), Rass = f.assignlit(-v);
		if (Lass || Rass) {
			if (Lass) {
				this.left = this.left.left;
				this.right = this.left.right;
				this.pn = this.left.pn;
				this.dn = this.left.dn;
				this.deep = this.left.deep;
				this.size = this.left.size;
			} else {
				this.left = this.right.left;
				this.right = this.right.right;
				this.pn = this.right.pn;
				this.dn = this.right.dn;
				this.deep = this.right.deep;
				this.size = this.right.size;
			}
			
			if (!this.isTerminal()) {
				this.left.parent = this;
				this.right.parent = this;
			}
			
			return this;
		}
		
		QDeepPNSLearnNode ret = null;
		int idx = 0;
		if (ret == null && !this.left.isSolved()) {
			ret = this.left;
			idx = 1;
		}
		
		if ((ret == null && !this.right.isSolved()) 
			|| (ret != null && ret.dpn() > this.right.dpn() && !this.right.isSolved())) {
			idx = -1;
			ret = this.right;
		}
		
		if (idx == 0) {
			MyLog.log(lm, 0, "no MPN!");
		}
		
		f.set(idx * this.splitnode.getVal());
		f.simplify();
		return ret;
	}
	
	
	private void prun(TwoWatchedLiteralFormula f) {
		PNSLearnReason reason = (PNSLearnReason)GlobalReason.GetReason();
		if (reason.status != PNSLearnReason.Status.unknown && reason.status != PNSLearnReason.Status.lock) {
			if (reason.satisfied) {
				this.pn = 0;
				this.dn = QDeepPNSBJNode.inf;
				if (!f.isMax(this.splitnode.getVal())) TwoWatchedLiteralFormula.prunU++;
			} else {
				this.dn = 0;
				this.pn = QDeepPNSBJNode.inf;
				if (f.isMax(this.splitnode.getVal())) TwoWatchedLiteralFormula.prunE++;
			}
		}
	}
	
	/**
	 * 
	 * @return true/false if the reason is changed from invalid to valid
	 */
	public boolean backpropagation(TwoWatchedLiteralFormula f) {
		if (this.isTerminal() || this.isSolved()) return false;
		List<QDeepPNSLearnNode> child = new ArrayList<>();
		child.add(this.left);
		child.add(this.right);
		QDeepPNSLearnNode curr = null;
		if (this.splitnode.isMax()) {
			this.pn = child.get(0).pn;
			this.dn = 0;
			for (QDeepPNSLearnNode c : child) {
				this.pn = Math.min(this.pn, c.getPn());
				this.dn += c.getDn();
				if ((curr == null && !c.isSolved()) || (curr != null && !c.isSolved() && c.dpn() <= curr.dpn()))  {
					curr = c;
				}
			}
		} else {
			this.pn = 0;
			this.dn = child.get(0).dn;
			for (QDeepPNSLearnNode c : child) {
				this.pn += c.getPn();
				this.dn = Math.min(this.dn, c.getDn());
				if ((curr == null && !c.isSolved()) || (curr != null && !c.isSolved() && c.dpn() <= curr.dpn())) {
					curr = c;
				}
			}
		}
		
		if (curr != null) {
			this.deep = curr.deep;
		}
		
		// TODO add code here for pruning
		if (!this.isSolved()) {
			prun(f);
		}
		
		this.size = this.left.size + this.right.size + 1;
		
		if (this.isSolved()) {
			ResultGenerator.getInstance().cutNode(this.left.size + this.right.size);
			this.size = 1;
			this.left = this.right = null;
			this.pn = Math.min(this.pn, QDeepPNSLearnNode.inf);
			this.dn = Math.min(this.dn, QDeepPNSLearnNode.inf);
			if (this.isWin()) {
				TwoWatchedLiteralFormula.truecount++;
			} else {
				TwoWatchedLiteralFormula.falsecount++;
			}
		}
		
		return true;
	}
}