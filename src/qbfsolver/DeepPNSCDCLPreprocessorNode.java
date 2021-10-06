package qbfsolver;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import qbfexpression.AdjacencyListClauseWithReason;
import qbfexpression.AdjacencyListFormulaCDCL;
import qbfexpression.Quantifier;

public class DeepPNSCDCLPreprocessorNode {
	private Quantifier splitnode;
	private DeepPNSCDCLPreprocessorNode left = null, right = null, parent = null;
	private int pn, dn, depth;
	private double deep;
	public DeepPNSCDCLPreprocessorNode(AdjacencyListFormulaCDCL f, int depth) {
		Result res = ResultGenerator.getInstance();
		res.setNode();
		this.deep = 1.0 / depth;
		this.depth = depth;
		this.left = this.right = this.parent = null;
		int val = f.evaluate();
		if (val == 1) {
			this.pn = 0;
			this.dn = PNSNode.inf;
		} else if (val == 0) {
			this.pn = PNSNode.inf;
			this.dn = 0;
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
	
	public DeepPNSCDCLPreprocessorNode getParent() {
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
		double R = 0.1;
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
	
	public void expansion(AdjacencyListFormulaCDCL f) {
		if (f.evaluate() != -1) {
			System.err.println("bad!, invalid expansion");
			System.exit(0);
		}
		
		//System.out.println("Expand " + this.splitnode.getVal());
		f.set(-this.splitnode.getVal());
		f.dropquantifier(this.splitnode.getVal());
		f.simplify();
		f.commit();
		DeepPNSCDCLPreprocessorNode L = new DeepPNSCDCLPreprocessorNode(f, this.depth + 1);
		L.parent = this;
		this.left = L;
		// print(f);
		//System.out.println(this.left.isSolved());
		f.undo();
		f.set(this.splitnode.getVal());
		f.dropquantifier(this.splitnode.getVal());
		f.simplify();
		f.commit();
		DeepPNSCDCLPreprocessorNode R = new DeepPNSCDCLPreprocessorNode(f, this.depth + 1);
		R.parent = this;
		this.right = R;
		f.undo();	
	}
	
	private void print(AdjacencyListFormulaCDCL f) {
		for (AdjacencyListClauseWithReason c : f.formula) {
			if (c.evaluate() == -1)
			System.out.println(c);
		}
	}
	
	public DeepPNSCDCLPreprocessorNode MPN(AdjacencyListFormulaCDCL f) {
		if (!f.isOuter(this.splitnode.getVal())) {
			System.out.println("change searching space " + this.splitnode.getVal() + " " + this.depth + " " + f.block);
			System.out.println("currentass= " + f.currentassign);
			System.exit(0);
			this.splitnode = f.peek();
			this.left = this.right = null;
			if (this.splitnode.isMax()) {
				this.pn = 1;
				this.dn = 2;
			} else {
				this.pn = 2;
				this.dn = 1;
			}
			try {
				CDCLPreprocessor.preprocess(f);
			} catch (IOException e) {
				e.printStackTrace();
			}
			return null;
		}
		
		if (this.isTerminal()) {
			try {
				CDCLPreprocessor.preprocess(f);
			} catch (IOException e) {
				e.printStackTrace();
			}
			return null;
		}
		
		//System.out.println("splitnode= " + this.splitnode);
		if (ResultGenerator.getCommandLine().getDebug()) {
			print(f);
		}
		
		
		f.set(-this.splitnode.getVal());
		f.dropquantifier(this.splitnode.getVal());
		f.simplify();
		f.commit();
		DeepPNSCDCLPreprocessorNode L = new DeepPNSCDCLPreprocessorNode(f, this.depth + 1);
		f.undo();
		f.set(this.splitnode.getVal());
		f.dropquantifier(this.splitnode.getVal());
		f.simplify();
		f.commit();
		DeepPNSCDCLPreprocessorNode R = new DeepPNSCDCLPreprocessorNode(f, this.depth + 1);
		f.undo();	
		
		if (L.isSolved() != this.left.isSolved() || R.isSolved() != this.right.isSolved()) {
			this.left = this.right = null;
			if (this.splitnode.isMax()) {
				this.pn = 1;
				this.dn = 2;
			} else {
				this.pn = 2;
				this.dn = 1;
			}
			
			try {
				CDCLPreprocessor.preprocess(f);
			} catch (IOException e) {
				e.printStackTrace();
			}
			return null;
		}
		
		
		
		DeepPNSCDCLPreprocessorNode ret = null;
		boolean debug = ResultGenerator.getCommandLine().getDebug();
		int idx = 0;
		if (ret == null && !this.left.isSolved()) {
			ret = this.left;
			idx = -1;
		}
		
		if (debug) {
			System.out.println(this.splitnode.isMax() ? "exist " : " universe");
		}
		
		if ((ret == null && !this.right.isSolved()) 
			|| (ret != null && ret.dpn() > this.right.dpn() && !this.right.isSolved())) {
			idx = 1;
			ret = this.right;
		}
		
		if (idx == 0) {
			System.err.println("no MPN!");
			System.exit(1);
		}
		
		
		if (idx == 1 && !this.left.isSolved()) {
			Random r = new Random();
			if (r.nextInt(7) == 0) {
				idx = -1;
				ret = this.left;
			}
		} else if (idx == -1 && !this.right.isSolved()) {
			Random r = new Random();
			if (r.nextInt(7) == 0) {
				idx = 1;
				ret = this.right;
			}
		}
		f.set(idx * this.splitnode.getVal());
		f.dropquantifier(this.splitnode.getVal());
		f.simplify();
		f.commit();
		// System.out.println("current assignment " + f.currentassign);
		//System.out.println(f);
		//System.out.println("assign " + idx * this.splitnode.getVal());
		//print(f);
		return ret;
	}
	/**
	 * 
	 * @return true/false if the reason is changed from invalid to valid
	 */
	public void backpropagation() {
		// System.out.println("backtrack");
		if (this.isTerminal() || this.isSolved()) return;
		List<DeepPNSCDCLPreprocessorNode> child = new ArrayList<>();
		child.add(this.left);
		child.add(this.right);
		DeepPNSCDCLPreprocessorNode curr = null;
		if (this.splitnode.isMax()) {
			this.pn = child.get(0).pn;
			this.dn = 0;
			for (DeepPNSCDCLPreprocessorNode c : child) {
				this.pn = Math.min(this.pn, c.getPn());
				this.dn += c.getDn();
				if ((curr == null && !c.isSolved()) || (curr != null && !c.isSolved() && c.dpn() <= curr.dpn()))  {
					curr = c;
				}
			}
		} else {
			this.pn = 0;
			this.dn = child.get(0).dn;
			for (DeepPNSCDCLPreprocessorNode c : child) {
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
		
		
		if (this.isSolved()) {
			this.left = this.right = null;
			this.pn = Math.min(this.pn, PNSNode.inf);
			this.dn = Math.min(this.dn, PNSNode.inf);
		}
	}
}	
