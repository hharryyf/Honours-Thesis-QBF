package qbfsolver;
import qbfexpression.*;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
//import java.io.FileWriter;
//import java.io.IOException;
import java.util.Scanner;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;


public class QdimacFileReader {
	public CnfExpression read(int type) throws FileNotFoundException {
		File myObj = new File("formula.txt");
		Scanner sc = new Scanner(myObj);
		String first = sc.nextLine();
		first = first.trim();
		String[] s = first.split("\\s+");
		int n = Integer.valueOf(s[2]);
		int m = Integer.valueOf(s[3]);
		CnfExpression ret = null;
		if (ResultGenerator.cdcl) {
			ret = new AdjacencyListFormulaCDCL(n, m);
		} else {
			ret = new AdjacencyListFormulaWithReason(n, m);
		}
		
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
	
	public static void main(String[] args) {
		Scanner sc = new Scanner(System.in);
		String first = sc.nextLine();
		first = first.trim();
		String[] s = first.split("\\s+");
		int n = Integer.valueOf(s[2]);
		int m = Integer.valueOf(s[3]);
		//CnfExpression ret = new AdjacencyListFormulaWithReason(n, m);
		ISolver solver = SolverFactory.newDefault();
		solver.setTimeout(900);
		solver.setExpectedNumberOfClauses(m);
		solver.newVar(n);
		int i;
		while (m > 0) {
			first = sc.nextLine();
			first = first.trim();
			s = first.split("\\s+");
			if (s[0].charAt(0) == 'e') {
				continue;
			} else if (s[0].charAt(0) == 'a') {
				continue;
			} else {
				// Disjunction c = new DisjunctionDefault();
				ArrayList<Integer> list = new ArrayList<>();
				for (i = 0 ; i < s.length; ++i) {
					if (Integer.valueOf(s[i]) != 0) {
						list.add(Integer.valueOf(s[i]));
					}
				}
				
				int [] clause = list.stream().mapToInt(Integer::intValue).toArray();
				try {
					solver.addClause(new VecInt(clause));
				} catch (ContradictionException e) {
					System.out.println("UNSAT");
				}
				
				try {
					boolean curr = solver.isSatisfiable();
					System.out.print(curr + " ");
					if (!curr) {
						sc.close();
						System.exit(0);
					} else {
						int[] res = solver.findModel();
						for (int j = 0 ; j < res.length; ++j) {
							System.out.print(res[j] + " ");
						}
						System.out.println();
					}
				} catch (TimeoutException e) {
					e.printStackTrace();
				}
				m--;
			}
		}
		sc.close();
	}
}