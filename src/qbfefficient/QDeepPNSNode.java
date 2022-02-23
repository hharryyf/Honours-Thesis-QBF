package qbfefficient;

import java.util.ArrayList;
import java.util.List;
import qbfexpression.Quantifier;
import qbfsolver.Result;
import qbfsolver.ResultGenerator;

public class QDeepPNSNode {
	protected static String lm = new String("QDeepPNSNode");
	Quantifier splitnode;
	int visited = 0;
	QDeepPNSNode left = null, right = null, parent = null;
	// reason exists if and only if the node has been proved/disproved
	ConflictSolution reason = null;
	int pn, dn, depth, size;
	double deep;
	boolean valid = false;
	public static int inf = 120000000;
	public QDeepPNSNode(TwoWatchedLiteralFormula f, int depth) {
		this.visited = 1;
		this.deep = 1.0 / depth;
		this.depth = depth;
		this.left = this.right = this.parent = null;
		Result rr = ResultGenerator.getInstance();
		rr.setNode();
		int val = f.evaluate();
		if (val == 1) {
			this.pn = 0;
			this.dn = QDeepPNSNode.inf;
			this.reason = f.getReason();
			this.valid = true;
			TwoWatchedLiteralFormula.truecount++;
		} else if (val == 0) {
			this.pn = QDeepPNSNode.inf;
			this.dn = 0;
			this.reason = f.getReason();
			this.valid = true;
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
	
	public ConflictSolution getReason() {
		return this.reason;
	}
	
	public QDeepPNSNode getParent() {
		return this.parent;
	}
	
	public boolean isTerminal() {
		return this.left == null && this.right == null;
	}
	
	public boolean isSolved() {
		return this.pn >= QDeepPNSNode.inf || this.dn >= QDeepPNSNode.inf;
	}
	
	public boolean isLost() {
		return this.pn >= QDeepPNSNode.inf;
	}
	
	public boolean isWin() {
		return this.dn >= QDeepPNSNode.inf;
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
		this.dn = QDeepPNSNode.inf;
	}
	
	protected void setFalse() {
		this.dn = 0;
		this.pn = QDeepPNSNode.inf;
	}
	
	public void prun() {
		if (this.reason == null || !this.valid) return;
		if (this.reason.satisfied) {
			setTrue();
		} else {
			setFalse();
		}
	}
	
	public void expansion(TwoWatchedLiteralFormula f) {
		if (f.evaluate() != -1) {
			MyLog.log(lm, 0, "bad!, invalid expansion");
		}
		// left split
		f.set(this.splitnode.getVal());
		f.simplify();
		QDeepPNSNode L = new QDeepPNSNode(f, this.depth + 1);
		L.parent = this;
		this.left = L;
		f.undo(this.left.reason);
		// right split
		f.set(-this.splitnode.getVal());
		f.simplify();
		QDeepPNSNode R = new QDeepPNSNode(f, this.depth + 1);
		R.parent = this;
		this.right = R;
		f.undo(this.right.reason);		
	}
	
	public QDeepPNSNode MPN(TwoWatchedLiteralFormula f) {
		if (this.isTerminal()) return null;
		QDeepPNSNode ret = null;
		int idx = 0;
		if (ret == null && !this.left.isSolved()) {
			ret = this.left;
			idx = 1;
		}
		
		// if (this.splitnode.getVal() != f.peek().getVal()) MyLog.log(lm, 0, "some pure literals are not eliminated");
		
		
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
	/**
	 * 
	 * @return true/false if the reason is changed from invalid to valid
	 */
	public boolean backpropagation(TwoWatchedLiteralFormula f) {
		if (this.isTerminal() || this.isSolved()) return false;
		List<QDeepPNSNode> child = new ArrayList<>();
		child.add(this.left);
		child.add(this.right);
		QDeepPNSNode curr = null;
		if (this.splitnode.isMax()) {
			this.pn = child.get(0).pn;
			this.dn = 0;
			for (QDeepPNSNode c : child) {
				this.pn = Math.min(this.pn, c.getPn());
				this.dn += c.getDn();
				if ((curr == null && !c.isSolved()) || (curr != null && !c.isSolved() && c.dpn() <= curr.dpn()))  {
					curr = c;
				}
			}
		} else {
			this.pn = 0;
			this.dn = child.get(0).dn;
			for (QDeepPNSNode c : child) {
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
		
		boolean changed = this.valid;
		// consider to merge the two calculated reason to the root
		if (!this.valid) {
			if (this.left.valid) {
				if (!this.right.isSolved()) {
					// case when the pruning condition can be triggered
					if (this.isSolved() || !this.left.reason.contains(this.splitnode.getVal())) {
						this.reason = this.left.reason;
						this.valid = true;
						if (!this.isSolved()) {
							if (f.isMax(this.splitnode.getVal())) {
								TwoWatchedLiteralFormula.prunE++;
							} else {
								TwoWatchedLiteralFormula.prunU++;
							}
						}
						this.prun();
					}
				} else {
					// both sides are solved
					// two possible cases
					if (this.isWin() == this.right.isWin() && this.isWin() == this.left.isWin()) {
						// here's when the resolution happens
						this.left.reason.resolve(this.right.reason, this.splitnode.getVal(), f);
						// we increment the number of resolution count by 1
						TwoWatchedLiteralFormula.rescount++;
						this.reason = this.left.reason;
					} else if (this.isWin() == this.right.isWin()) {
						if (this.right.reason.contains(-this.splitnode.getVal())) {
							this.right.reason.resolve(this.left.reason, this.splitnode.getVal(), f);
							// we increment the number of resolution count by 1
							TwoWatchedLiteralFormula.rescount++;
						}
						this.reason = this.right.reason;
					} else if (this.isWin() == this.left.isWin()) {
						if (this.left.reason.contains(this.splitnode.getVal())) {
							this.left.reason.resolve(this.right.reason, this.splitnode.getVal(), f);
							// we increment the number of resolution count by 1
							TwoWatchedLiteralFormula.rescount++;
						}
						this.reason = this.left.reason;
					} else {
						MyLog.log(lm, 0, "invalid logic!");
					}
					this.valid = true; 
				}
			} else if (this.right.valid) {
				if (this.isSolved() || !this.right.reason.contains(-this.splitnode.getVal())) {
					this.reason = this.right.reason;
					this.valid = true;
					if (!this.isSolved()) {
						if (f.isMax(this.splitnode.getVal())) {
							TwoWatchedLiteralFormula.prunE++;
						} else {
							TwoWatchedLiteralFormula.prunU++;
						}
					}
					this.prun();
				}
			}
		}
		
		this.size = this.left.size + this.right.size + 1;
		
		if (this.isSolved()) {
			ResultGenerator.getInstance().cutNode(this.left.size + this.right.size);
			this.size = 1;
			this.left = this.right = null;
			this.pn = Math.min(this.pn, QDeepPNSNode.inf);
			this.dn = Math.min(this.dn, QDeepPNSNode.inf);
			if (this.isWin()) {
				TwoWatchedLiteralFormula.truecount++;
			} else {
				TwoWatchedLiteralFormula.falsecount++;
			}
		}
		
		return changed != this.valid;
	}
}
