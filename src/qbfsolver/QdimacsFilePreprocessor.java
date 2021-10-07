package qbfsolver;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Scanner;
import qbfexpression.AdjacencyListClauseWithReason;
import qbfexpression.AdjacencyListFormulaWithReason;
import qbfexpression.Disjunction;
import qbfexpression.Quantifier;
import utilstructure.Pair;

public class QdimacsFilePreprocessor {
	public void preprocess() {
		Scanner sc = new Scanner(System.in);
		String first = sc.nextLine();
		first = first.trim();
		String[] s = first.split("\\s+");
		int n = Integer.valueOf(s[2]);
		int m = Integer.valueOf(s[3]);
		AdjacencyListFormulaWithReason ret = new AdjacencyListFormulaWithReason(n, m);
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
				Disjunction c = new AdjacencyListClauseWithReason();
				List<Pair<Integer, Integer>> list = new ArrayList<>();
				HashSet<Integer> st = new HashSet<>();
				for (i = 0 ; i < s.length; ++i) {
					if (Integer.valueOf(s[i]) != 0) {
						st.add(Integer.valueOf(s[i]));
						list.add(new Pair<>(ret.getLevel(Integer.valueOf(s[i])), Integer.valueOf(s[i])));
					}
				}
				
				Collections.sort(list);
				
				while (!list.isEmpty() && !ret.isMax(list.get(list.size() - 1).second)) {
					list.remove(list.size() - 1);
				}
				
				boolean trivial = false;
				for (Pair<Integer, Integer> v : list) {
					c.add(v.second);
					if (st.contains(-v.second)) {
						trivial = true;
					}
				}
				
				if (!trivial) {
					if (!c.isEmpty()) {
						ret.addcnf(c);
					} else {
						ret.setSatisfied(false);
					}
				}
				m--;
			}
		}
		sc.close();
		ret.normalize();
		try {
			FileWriter myWriter = new FileWriter("formula.txt");
			System.out.println("finish preprocessing");
			myWriter.write(ret.toString());
			myWriter.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public static void main(String args[]) {
		QdimacsFilePreprocessor reader = new QdimacsFilePreprocessor();
		reader.preprocess();
	}
}
