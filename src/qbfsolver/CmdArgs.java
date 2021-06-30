package qbfsolver;

public class CmdArgs {
	private int type = 0;
	private int bfU = 3;
	private int bfE = 3;
	private boolean debug = false;
	public CmdArgs() {
		
	}
	
	public boolean getDebug() {
		return debug;
	}
	
	public CmdArgs(int type) {
		this.type = type;
	}
	
	public double getR() {
		int iter = ResultGenerator.getInstance().getNode();
		double ret = 0.0;
		if (((iter / 10000) & 1) == 1) ret = 0.5;
		//if (iter % 100000 > 99990) ret = 1.0;
		return ret;
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