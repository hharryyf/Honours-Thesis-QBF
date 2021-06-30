package qbfsolver;

public class ResultGenerator {
	private static Result ret = null;
	private static CmdArgs cmd = null;
	public static boolean satsolver = true;
	public static boolean bomh = false;
	public static boolean variate = false;
	public static Result getInstance() {
		if (ret == null) {
			ret = new Result();
		}
		return ret;
	}
	
	public static CmdArgs getCommandLine() {
		if (cmd == null) {
			cmd = new CmdArgs();
		}
		return cmd;
	}
}