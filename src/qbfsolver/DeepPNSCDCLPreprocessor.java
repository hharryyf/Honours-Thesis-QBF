package qbfsolver;

import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Stack;
import qbfexpression.AdjacencyListFormulaCDCL;
import qbfexpression.CnfExpression;
import qbfexpression.Conflict;

public class DeepPNSCDCLPreprocessor implements Solver {
	
	private int maxT = 1200;
	
	@Override
	public boolean solve(CnfExpression g) {
		if (g.getClass() != AdjacencyListFormulaCDCL.class) {
			System.err.println("wrong type");
			System.exit(0);
		}
		
		AdjacencyListFormulaCDCL f = (AdjacencyListFormulaCDCL) g;
		DeepPNSCDCLPreprocessorNode root = new DeepPNSCDCLPreprocessorNode(f, 1), curr = root;
		int i = 0, tolvisited = 0;
		Stack<AdjacencyListFormulaCDCL> stk = new Stack<>();
		while (i <= this.maxT && !root.isSolved()) {
			if (i % 1 == 0) {
				System.out.println("Iteration #" + i + " pn = " + root.getPn() + " dn= " + root.getDn());
			}
					
			if (stk.empty()) {
				stk.push(f);
			}
					
			AdjacencyListFormulaCDCL fp = stk.peek();
			if (curr == root) {
				try {
				 	f.learn();
					int val = f.evaluate();
					if (val == 0) {
						root.setFalse();
					} else if (val == 1) {
						root.setTrue();
					}
				} catch (IOException e) {
					e.printStackTrace();
				} 
				
			}
			
			if (root.isSolved()) break;
			
			DeepPNSCDCLPreprocessorNode it;
			while (true) {
				it = curr.MPN(fp);
				if (it == null) break;
				stk.push(fp);
				curr = it;
				tolvisited++;
			}
			
			curr.expansion(fp);
			while (curr != null) {
				int pn = curr.getPn(), dn = curr.getDn();
				curr.backpropagation();
				if (((Conflict) f.conflict).counter == 0 || ((Conflict) f.conflict).counter == -2) {
					if (pn == curr.getPn() && dn == curr.getDn()) break;
				}
				if (curr != root) {
					if (!stk.isEmpty()) {
						stk.peek().undo();
					}
					curr = curr.getParent();
					stk.pop();
				}
				
				tolvisited++;
				if (curr == root) break;
			}
					
			i++;
		}
		Result res = ResultGenerator.getInstance();
		System.out.println("Iteration " + i + " pn = " + root.getPn() + " dn= " + root.getDn());
		System.out.println("Tolvisited = " + tolvisited);
		res.setIteration(i);
		if (root.isWin()) {
			res.setTruth(true);
			FileWriter myWriter;
			try {
				myWriter = new FileWriter("formula.txt");
				myWriter.write("p cnf 1 0\n");
				myWriter.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
			return true;
		}
		
		if (root.isLost()) {
			res.setTruth(false);
			FileWriter myWriter;
			try {
				myWriter = new FileWriter("formula.txt");
				myWriter.write("p cnf 1 1\n0\n");
				myWriter.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
			return false;
		}
		
		res.setIteration(maxT + 1);
		while (curr != root) {
			f.undo();
			curr = curr.getParent();
		}
		
		try {
			f.learn();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		
		FileWriter myWriter;
		try {
			myWriter = new FileWriter("formula.txt");
			myWriter.write(f.toString());
			myWriter.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		System.out.println("finish learning!");
		System.exit(0);
		return false;
	}
	
	public static void main(String[] args) throws FileNotFoundException {
		QdimacsFilePreprocessor p = new QdimacsFilePreprocessor(); 
    	QdimacFileReader rd = new QdimacFileReader();
		CnfExpression fo;
		p.preprocess();
		ResultGenerator.cdcl = true;
		fo = rd.read(0);
		AdjacencyListFormulaCDCL f = (AdjacencyListFormulaCDCL) fo;
		Solver s = new DeepPNSCDCLPreprocessor();
		s.solve(f);
	}

}
