package qbfefficient;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import qbfexpression.Quantifier;
import qbfsolver.Result;
import qbfsolver.ResultGenerator;

public class QDeepPNSCDCLSBJNode {
	protected static String lm = new String("QDeepPNSCDCLSBJNode");
	Quantifier splitnode;
	int visited = 0;
	ConflictSolution reason;
	QDeepPNSCDCLSBJNode left = null, right = null, parent = null;
	int pn, dn, depth, size;
	double deep;
	public static int inf = 120000000;
	public QDeepPNSCDCLSBJNode(TwoWatchedLiteralFormula f, int depth) {
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
	
	public QDeepPNSCDCLSBJNode getParent() {
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
		int val = f.evaluate();
		if (this.isSolved() || val != -1) {
			if (this.isSolved()) MyLog.log(lm, 2, "reach a solved node");
			if (val != -1) {
				if (val == 1) {
					this.pn = 0;
					this.dn = QDeepPNSBJNode.inf;
					TwoWatchedLiteralFormula.truecount++;
					//GlobalReason.setReason((PNSLearnReason) f.getReason());
					this.reason = f.getReason();
				
				} else if (val == 0) {
					this.pn = QDeepPNSBJNode.inf;
					this.dn = 0;
					TwoWatchedLiteralFormula.falsecount++;
					// GlobalReason.setReason((PNSLearnReason) f.getReason());
					this.reason = f.getReason();
				}
				MyLog.log(lm, 2, "reach a SAT/UNSAT node");
			}
			return;
		}
		
		if (!this.isTerminal()) MyLog.log(lm, 0, "Tree structure is wrong, try to expand non-leaf node");
		MyLog.log(lm, 2, "branching variable", this.splitnode.getVal());
		// peek a new quantifier
		if (f.isassigned(this.splitnode.getVal())) {
			this.splitnode = f.peek();
			MyLog.log(lm, 2, "change branching variable to", this.splitnode);
		}
		// left split
		f.set(this.splitnode.getVal());
		f.simplify();
		QDeepPNSCDCLSBJNode L = new QDeepPNSCDCLSBJNode(f, this.depth + 1);
		MyLog.log(lm, 2, "create new node", L);
		L.parent = this;
		this.left = L;
		if (this.left.isSolved()) {
			this.left.reason = f.getReason();
		}
		f.undo(null);
		// right split
		f.set(-this.splitnode.getVal());
		f.simplify();
		QDeepPNSCDCLSBJNode R = new QDeepPNSCDCLSBJNode(f, this.depth + 1);
		R.parent = this;
		MyLog.log(lm, 2, "create new node", R);
		this.right = R;
		if (this.right.isSolved()) {
			this.right.reason = f.getReason();
		}
		f.undo(null);
	}
	
	public QDeepPNSCDCLSBJNode MPN(TwoWatchedLiteralFormula f) {
		if (this.isTerminal() || this.isSolved()) {
			if (this.isTerminal()) MyLog.log(lm, 2, "MPN reach a terminal node", this);
			if (this.isSolved()) MyLog.log(lm, 2, "MPN reach a solved node", this);
			return null;
		}
		
		int val = f.evaluate();
		if (val != -1) {
			MyLog.log(lm, 2, "MPN is a solved node", f.assign.assignment);
			if (val == 1) {
				this.pn = 0;
				this.dn = QDeepPNSBJNode.inf;
				TwoWatchedLiteralFormula.truecount++;
				this.reason = f.getReason();
			} else if (val == 0) {
				this.pn = QDeepPNSBJNode.inf;
				this.dn = 0;
				TwoWatchedLiteralFormula.falsecount++;
				this.reason = f.getReason();
			}
			this.left = this.right = null;
			return null;
		}
		MyLog.log(lm, 2, "select MPN", this.splitnode.getVal(), "address", this);
		int v = this.splitnode.getVal();
		boolean Lass = f.assignlit(v), Rass = f.assignlit(-v);
		if (Lass || Rass) {
			MyLog.log(lm, 2, "Scholter method", Lass ? "left assign" : "right assign");
			if (Lass) {
				this.pn = this.left.pn;
				this.dn = this.left.dn;
				this.reason = this.left.reason;
				this.splitnode = this.left.splitnode;
				this.deep = this.left.deep;
				this.size = this.left.size;
				this.right = this.left.right;
				this.left = this.left.left;
			} else {
				this.pn = this.right.pn;
				this.dn = this.right.dn;
				this.reason = this.right.reason;
				this.splitnode = this.right.splitnode;
				this.deep = this.right.deep;
				this.size = this.right.size;
				this.left = this.right.left;
				this.right = this.right.right;
			}
			
			if (!this.isTerminal()) {
				this.left.parent = this;
				this.right.parent = this;
			}
			
			return this;
		}
		
		QDeepPNSCDCLSBJNode ret = null;
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
		
		Random r = new Random();
		if (TwoWatchedLiteralFormula.preprocess == true && !left.isSolved() && !right.isSolved() && 1 == r.nextInt(100)) {
			if (ret == this.left) {
				ret = this.right;
			} else {
				ret = this.left;
			}
			idx *= -1;
		}
		if (idx == 0) {
			MyLog.log(lm, 0, "no MPN!");
		}
		
		if (ret.isSolved()) MyLog.log(lm, 0, "MPN is a solved node");
		f.set(idx * this.splitnode.getVal());
		f.simplify();
		
		MyLog.log(lm, 2, "get mpn address", ret);
		return ret;
	}
	
	
	private void prun(TwoWatchedLiteralFormula f, ConflictSolution L, ConflictSolution R) {
		ConflictSolutionCDCLSBJPNS lreason = cast(L), rreason = cast(R);
		MyLog.log(lm, 2, "resolve ", lreason, rreason, lreason != null ? lreason.satisfied : "Unknown", rreason != null ? rreason.satisfied : "Unknown");
		if (lreason == null && rreason == null) return;
		if (lreason != null && rreason == null) {
			// check if the lreason can produce pruning
			if (lreason.satisfied) {
				if (this.splitnode.isMax() || (!this.splitnode.isMax() && !lreason.contains(this.splitnode.getVal()))) {
					this.reason = lreason;
					this.setTrue();
				}
			} else {
				if (!this.splitnode.isMax() || (this.splitnode.isMax() && !lreason.contains(-this.splitnode.getVal()))) {
					this.reason = lreason;
					this.setFalse();
				}
			}
		} else if (lreason == null && rreason != null) {
			if (rreason.satisfied) {
				if (this.splitnode.isMax() || (!this.splitnode.isMax() && !rreason.contains(-this.splitnode.getVal()))) {
					this.reason = rreason;
					this.setTrue();
				}
			} else {
				if (!this.splitnode.isMax() || (this.splitnode.isMax() && !rreason.contains(this.splitnode.getVal()))) {
					this.reason = rreason;
					this.setFalse();
				}
			}
		} else {
			if (lreason.satisfied && !rreason.satisfied) {
				if (this.splitnode.isMax()) {
					this.reason = lreason;
				} else {
					this.reason = rreason;
				}
			} else if (!lreason.satisfied && rreason.satisfied) {
				if (this.splitnode.isMax()) {
					this.reason = rreason;
				} else {
					this.reason = lreason;
				}
			} else if (lreason.satisfied && rreason.satisfied) {
				if (this.splitnode.isMax()) {
					this.reason = lreason;
				} else {
					if (!lreason.contains(this.splitnode.getVal())) {
						this.reason = lreason;
					} else if (!rreason.contains(-this.splitnode.getVal())) {
						this.reason = rreason;
					} else {
						lreason.resolve(rreason, this.splitnode.getVal(), f);
						this.reason = lreason;
					}
				}
			} else {
				if (!this.splitnode.isMax()) {
					this.reason = lreason;
				} else {
					if (!lreason.contains(-this.splitnode.getVal())) {
						this.reason = lreason;
					} else if (!rreason.contains(this.splitnode.getVal())) {
						this.reason = rreason;
					} else {
						lreason.resolve(rreason, this.splitnode.getVal(), f);
						this.reason = lreason;
					}
				}
			}
		}
		
		MyLog.log(lm, 2, "result", this.reason, f.assign.assignment);
		// System.out.println("resolve" + L + " :: " + R + " get: " + this.reason + " split node: " + this.splitnode.getVal());
	}
	
	private ConflictSolutionCDCLSBJPNS cast(ConflictSolution r) {
		if (r == null) return null;
		return (ConflictSolutionCDCLSBJPNS) r;
	}
	
	/**
	 * 
	 * @return true/false if the reason is changed from invalid to valid
	 */
	public boolean backpropagation(TwoWatchedLiteralFormula f) {
		if (this.isTerminal() || this.isSolved()) return false;
		List<QDeepPNSCDCLSBJNode> child = new ArrayList<>();
		MyLog.log(lm, 3, "back propagation", this.splitnode.getVal());
		child.add(this.left);
		child.add(this.right);
		QDeepPNSCDCLSBJNode curr = null;
		if (this.splitnode.isMax()) {
			this.pn = child.get(0).pn;
			this.dn = 0;
			for (QDeepPNSCDCLSBJNode c : child) {
				this.pn = Math.min(this.pn, c.getPn());
				this.dn += c.getDn();
				if ((curr == null && !c.isSolved()) || (curr != null && !c.isSolved() && c.dpn() <= curr.dpn()))  {
					curr = c;
				}
			}
		} else {
			this.pn = 0;
			this.dn = child.get(0).dn;
			for (QDeepPNSCDCLSBJNode c : child) {
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
		
		ConflictSolution L = null;
		ConflictSolution R = null;
		
		if (this.left.reason != null) {
			f.set(this.splitnode.getVal());
			f.simplify();
			if (f.evaluate() != -1) {
				L = f.getReason();
				MyLog.log(lm, 2, "we meet an UNSAT node left");
			} else {
				L = cast(this.left.reason).duplicate();
				MyLog.log(lm, 2, "we meet a reason internally left");
			}
			f.undo(L);
		}
		
		if (this.right.reason != null) {
			f.set(-this.splitnode.getVal());
			f.simplify();
			if (f.evaluate() != -1) {
				R = f.getReason();
				MyLog.log(lm, 2, "we meet an UNSAT node right");
			} else {
				R = cast(this.right.reason).duplicate();
				MyLog.log(lm, 2, "we meet a reason internally right");
			}
			f.undo(R);
		}
		
		boolean ok = this.isSolved();
		prun(f, L, R);
		if (!ok && this.isSolved()) {
			if (this.splitnode.isMax()) {
				TwoWatchedLiteralFormula.prunE += 1;
			} else {
				TwoWatchedLiteralFormula.prunU += 1;
			}
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
		MyLog.log(lm, 3, this.pn, ", ", this.dn);
		
		return true;
	}
}
