package qbfsolver;

public class ResultGenerator {
	private static Result ret = null;
	private static CmdArgs cmd = null;
	public static boolean satsolver = false;
	public static boolean cdcl = false;
	public static boolean learnpreprocess = false;
	public static boolean nopure = false;
	public static boolean bomh = false;
	public static boolean dlis = false;
	public static boolean rand = false;
	public static boolean variate = false;
	public static boolean randomplayout = true;
	public static int maximumLearn = 2000;
	public static int triviallimit = 20;
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