package qbfsolver;

import java.util.ArrayList;
import java.util.List;

import qbfexpression.AdjacencyListFormula;
import qbfexpression.Quantifier;
import qbfexpression.Reason;

public class PNSNodeWithReason {
	private Quantifier splitnode;
	private PNSNodeWithReason left = null, right = null, parent = null;
	// reason exists if and only if the node has been proved/disproved
	private Reason reason = null;
	private int pn, dn, depth;
	private double deep;
	private boolean valid = false;
	public PNSNodeWithReason(AdjacencyListFormula f, int depth) {
		Result res = ResultGenerator.getInstance();
		res.setNode();
		this.deep = 1.0 / depth;
		this.depth = depth;
		this.left = this.right = this.parent = null;
		int val = f.evaluate();
		if (val == 1) {
			this.pn = 0;
			this.dn = PNSNode.inf;
			this.reason = f.getReason();
			this.valid = true;
		} else if (val == 0) {
			this.pn = PNSNode.inf;
			this.dn = 0;
			this.reason = f.getReason();
			this.valid = true;
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
	}
	
	public Reason getReason() {
		return this.reason;
	}
	
	public PNSNodeWithReason getParent() {
		return this.parent;
	}
	
	public boolean isTerminal() {
		return this.left == null && this.right == null;
	}
	
	public boolean isSolved() {
		return this.pn >= PNSNode.inf || this.dn >= PNSNode.inf;
	}
	
	public boolean isLost() {
		return this.pn >= PNSNode.inf;
	}
	
	public boolean isWin() {
		return this.dn >= PNSNode.inf;
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
		this.dn = PNSNode.inf;
	}
	
	protected void setFalse() {
		this.dn = 0;
		this.pn = PNSNode.inf;
	}
	
	public void prun() {
		if (this.reason == null || !this.valid) return;
		if (this.reason.satisfied) {
			setTrue();
		} else {
			setFalse();
		}
		this.left = this.right = null;
	}
	
	public void expansion(AdjacencyListFormula f) {
		if (f.evaluate() != -1) {
			System.err.println("bad!, invalid expansion");
			System.exit(0);
		}
		// left split
		f.set(this.splitnode.getVal());
		f.dropquantifier(this.splitnode.getVal());
		f.simplify();
		f.commit();
		PNSNodeWithReason L = new PNSNodeWithReason(f, this.depth + 1);
		L.parent = this;
		this.left = L;
		f.undo(this.left.reason);
		// right split
		f.set(-this.splitnode.getVal());
		f.dropquantifier(this.splitnode.getVal());
		f.simplify();
		f.commit();
		PNSNodeWithReason R = new PNSNodeWithReason(f, this.depth + 1);
		R.parent = this;
		this.right = R;
		f.undo(this.right.reason);		
	}
	
	public PNSNodeWithReason MPN(AdjacencyListFormula f) {
		if (this.isTerminal()) return null;
		PNSNodeWithReason ret = null;
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
			System.err.println("no MPN!");
			System.exit(1);
		}
		
		f.set(idx * this.splitnode.getVal());
		f.simplify();
		f.commit();
		return ret;
	}
	/**
	 * 
	 * @return true/false if the reason is changed from invalid to valid
	 */
	public boolean backpropagation() {
		if (this.isTerminal() || this.isSolved()) return false;
		List<PNSNodeWithReason> child = new ArrayList<>();
		child.add(this.left);
		child.add(this.right);
		PNSNodeWithReason curr = null;
		if (this.splitnode.isMax()) {
			this.pn = child.get(0).pn;
			this.dn = 0;
			for (PNSNodeWithReason c : child) {
				this.pn = Math.min(this.pn, c.getPn());
				this.dn += c.getDn();
				if ((curr == null && !c.isSolved()) || (curr != null && !c.isSolved() && c.dpn() <= curr.dpn()))  {
					curr = c;
				}
			}
		} else {
			this.pn = 0;
			this.dn = child.get(0).dn;
			for (PNSNodeWithReason c : child) {
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
						this.prun();
					}
				} else {
					// both sides are solved
					// two possible cases
					if (this.isWin() == this.right.isWin() && this.isWin() == this.left.isWin()) {
						// here's when the resolution happens
						this.left.reason.resolve(this.right.reason, this.splitnode.getVal());
						this.reason = this.left.reason;
					} else if (this.isWin() == this.right.isWin()) {
						this.right.reason.resolve(this.left.reason, this.splitnode.getVal());
						this.reason = this.right.reason;
					} else if (this.isWin() == this.left.isWin()) {
						this.left.reason.resolve(this.right.reason, this.splitnode.getVal());
						this.reason = this.left.reason;
					} else {
						System.err.println("invalid!");
						System.exit(1);
					}
					this.valid = true; 
				}
			} else if (this.right.valid) {
				if (this.isSolved() || !this.right.reason.contains(this.splitnode.getVal())) {
					this.reason = this.right.reason;
					this.valid = true;
					this.prun();
				}
			}
		}
		
		if (this.isSolved()) {
			this.left = this.right = null;
			this.pn = Math.min(this.pn, PNSNode.inf);
			this.dn = Math.min(this.dn, PNSNode.inf);
		}
		
		return changed != this.valid;
	}
}
