package qbfefficient;

import java.io.FileWriter;
import java.io.IOException;
import java.time.LocalTime;

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
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PBJ) {
			return "[PBJ] ";
		}  else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PL) {
			return "[PL] ";
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.P_CDCLSBJ) {
			return "[PCDCLSBJ] ";
		}
		
		return "[Preprocess] ";
	}
	
	public static String GetSolverNobracket() {
		if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BT) {
			return "BT";
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BJ) {
			return "BJ";
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.CDCLSBJ) {
			return "CDCLSBJ";
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.QCDCL) {
			return "QCDCL";
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PBJ) {
			return "PBJ";
		}  else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PL) {
			return "PL";
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.P_CDCLSBJ) {
			return "PCDCLSBJ";
		}
		
		return "Preprocess";
	}
	
	public static String GetLevel(int level) {
		if (level == 0) return "[ERROR]: ";
		if (level == 1) return "[INFO]: ";
		if (level == 2) return "[DEBUG]: ";
		return "[DEBUG2]: ";
	}
	
	public static void log_final(double d,long memo) {
		try {
			fout = new FileWriter("info.txt", true);
		} catch (IOException e) {
				e.printStackTrace();
				System.exit(1);
		}
		
		try {
			fout.write(GetSolverNobracket() + ","+ Double.toString(d) + "," + Long.toString(memo) + "\n");
			fout.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public static void log(String Module, int level, Object... msg) {
		
		if (level > TwoWatchedLiteralFormula.maxLevel) return;
		
		if (level < 0) {
			for (Object obj : msg) {
				System.out.print(obj);
				System.out.print(" ");
			}
			System.out.println();
			return;
		}
		
		try {
			fout = new FileWriter("log.txt", true);
		} catch (IOException e) {
				e.printStackTrace();
				System.exit(1);
		}
		
		try {
			LocalTime myObj = LocalTime.now();
		    fout.write("[" + myObj + "] " +  GetSolver() + "[" + Module + "] " + GetLevel(level));
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
