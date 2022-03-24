package qbfsolver;

import qbfefficient.TwoWatchedLiteralFormula;

public class CmdArgs {
	private int type = 0;
	private int bfU = 3;
	private int bfE = 3;
	private boolean debug = false;
	private double R = 0.0;
	public CmdArgs() {
		
	}
	
	public boolean getDebug() {
		return debug;
	}
	
	public CmdArgs(int type) {
		this.type = type;
	}
	
	public double getR() {
		return this.R;
	}
	
	public void setR(boolean ok) {
		if (ok) {
			int iter = ResultGenerator.getInstance().getNode();
			this.R = 0.0;
			if (ResultGenerator.getInstance().getLiveNode() >= TwoWatchedLiteralFormula.max_node_in_memory) {
				return;
			}
			if (((iter / 10000) & 1) == 1) this.R= 0.5;
		} else {
			int iter = ResultGenerator.getInstance().getNode();
			this.R = 0.0;
			if (ResultGenerator.getInstance().getLiveNode() >= TwoWatchedLiteralFormula.max_node_in_memory) {
				return;
			}
			if (((iter / 10000) & 1) == 1) this.R= 1.0;
		}
	}

	
	public int getBfE() {
		return this.bfE;
	}
	
	public int getBfU() {
		return this.bfU;
	}
	
	public void setBfE(int val) {
		this.bfE = val;
		this.bfE = Math.max(bfE, 1);
		this.bfE = Math.min(4, this.bfE);
	}
	
	public void setBfU(int val) {
		this.bfU = val;
		this.bfU = Math.max(bfU, 1);
		this.bfU = Math.min(4, this.bfU);
	}
	
	public int getType() {
		return this.type;
	}
	
	public void setType(int val) {
		this.type = val;
	}
}