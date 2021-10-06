package qbfsolver;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Random;

import qbfexpression.AdjacencyListClauseWithReason;
import qbfexpression.AdjacencyListFormulaCDCL;
import qbfexpression.CnfExpression;
import qbfexpression.Quantifier;

public class CDCLPreprocessor {
	public static void preprocess(AdjacencyListFormulaCDCL f) throws IOException {
		int v = f.evaluate();
		if (v == -1) {
			if (f.block.size() == 0) {
				System.err.println("wrong answer! inconsistent preprocessing result");
				FileWriter myWriter = new FileWriter("formula.txt");
				myWriter.write(f.fcount + " " + f.formula.size() + " " + f.proved + "\n");
				myWriter.write(f.block.toString() + "\n");
				for (AdjacencyListClauseWithReason cc : f.formula) {
					myWriter.write(cc.toString() + "\n");
				}
				myWriter.close();
				System.exit(0);
			}
			Quantifier q = f.peek();
			Random r = new Random();
			int idx = r.nextInt(2) == 0 ? 1 : -1;
			f.set(q.getVal() * idx);
			f.dropquantifier(q.getVal());
			f.simplify();
			f.commit();
			preprocess(f);
			f.undo();
		} else if (v == 0) {
			f.getConflict();
		} else {
			return;
		}
	}
	
	public static void main(String[] args) throws IOException {
		int i;
		QdimacsFilePreprocessor p = new QdimacsFilePreprocessor(); 
    	QdimacFileReader rd = new QdimacFileReader();
		CnfExpression fo;
		p.preprocess();
		ResultGenerator.cdcl = true;
		fo = rd.read(0);
		for (i = 0 ; i < 1000; ++i) {
			System.out.println("round " + i);
			preprocess((AdjacencyListFormulaCDCL) fo);
			AdjacencyListFormulaCDCL f = (AdjacencyListFormulaCDCL) fo;
			f.learn();
		}
		
		try {
			FileWriter myWriter = new FileWriter("formula.txt");
			System.out.println("finish learning preprocessing");
			myWriter.write(fo.toString());
			myWriter.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
