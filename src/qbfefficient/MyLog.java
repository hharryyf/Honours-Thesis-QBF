package qbfefficient;

import java.io.FileWriter;
import java.io.IOException;

public class MyLog {
	public static FileWriter fout;
	
	public static String GetSolver() {
		if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BT) {
			return "[BT] ";
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BJ) {
			return "[BJ] ";
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.CDCLSBJ) {
			return "[CDCLSBJ] ";
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.QCDCL) {
			return "[QCDCL] ";
		}
		
		return "[UNKNOWN] ";
	}
	
	public static String GetLevel(int level) {
		if (level == 0) return "[ERROR]: ";
		if (level == 1) return "[INFO]: ";
		if (level == 2) return "[DEBUG]: ";
		return "[DEBUG2]: ";
	}
	
	public static void log(String Module, int level, Object... msg) {
		
		if (level > TwoWatchedLiteralFormula.maxLevel) return;
		
		try {
			fout = new FileWriter("log.txt", true);
		} catch (IOException e) {
				e.printStackTrace();
				System.exit(1);
		}
		
		try {
			fout.write(GetSolver() + "[" + Module + "] " + GetLevel(level));
			for (Object obj : msg) {
				fout.write(obj + " ");
			}
			fout.write("\n");
			fout.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		if (level == 0) {
			System.exit(1);
		}
	}
}
