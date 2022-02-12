package qbfefficient;

import java.io.FileWriter;
import java.io.IOException;

public class MyLog {
	public static int numcall = 0;
	public static FileWriter fout;
	public static void log(String Module, boolean error, String msg) {
		if (numcall == 0) {
			try {
				fout = new FileWriter("log.txt", true);
			} catch (IOException e) {
				e.printStackTrace();
				System.exit(1);
			}
		}
		numcall = 1;
	
		if (!error) {
			try {
				fout.write("[" + Module + "] " + "[INFO]: " + msg + "\n");
			} catch (IOException e) {
				e.printStackTrace();
				System.exit(1);
			}
		} else {
			try {
				fout.write("[" + Module + "] " + "[ERROR]: " + msg + "\n");
			} catch (IOException e) {
				e.printStackTrace();
			}
			System.exit(1);
		}
	}
}
