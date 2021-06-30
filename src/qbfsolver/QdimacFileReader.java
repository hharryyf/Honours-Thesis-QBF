package qbfsolver;
import qbfexpression.*;

import java.io.File;
import java.io.FileNotFoundException;
//import java.io.FileWriter;
//import java.io.IOException;
import java.util.Scanner;

public class QdimacFileReader {
	public CnfExpression read(int type) throws FileNotFoundException {
		File myObj = new File("formula.txt");
		Scanner sc = new Scanner(myObj);
		String first = sc.nextLine();
		first = first.trim();
		String[] s = first.split("\\s+");
		int n = Integer.valueOf(s[2]);
		int m = Integer.valueOf(s[3]);
		CnfExpression ret = new AdjacencyListFormulaWithReason(n, m);
		int i;
		while (m > 0) {
			first = sc.nextLine();
			first = first.trim();
			s = first.split("\\s+");
			if (s[0].charAt(0) == 'e') {
				for (i = 1; i < s.length; ++i) {
					int val = Integer.valueOf(s[i]);
					if (val != 0) {
						Quantifier q = new Quantifier(true, val);
						ret.addquantifier(q);
					}
				}
			} else if (s[0].charAt(0) == 'a') {
				for (i = 1; i < s.length; ++i) {
					int val = Integer.valueOf(s[i]);
					if (val != 0) {
						Quantifier q = new Quantifier(false, val);
						ret.addquantifier(q);
					}
				}
			} else {
				// Disjunction c = new DisjunctionDefault();
				Disjunction c = new AdjacencyListClauseWithReason();
				for (i = 0 ; i < s.length; ++i) {
					if (Integer.valueOf(s[i]) != 0) {
						c.add(Integer.valueOf(s[i]));
					}
				}
				
				if (!c.isEmpty()) {
					ret.addcnf(c);
				} else {
					System.out.println("try to insert an empty clause");
					System.out.println("UNSAT");
					System.exit(0);
					ret.setSatisfied(false);
				}
				m--;
			}
		}
		sc.close();
		ret.normalize();		
		return ret;
	}
}