package qbfexpression;

import java.util.Comparator;

public class FormulaComparator implements Comparator<AdjacencyListClauseWithReason> {

	@Override
	public int compare(AdjacencyListClauseWithReason arg0, AdjacencyListClauseWithReason arg1) {
		Integer v1 = arg0.getSize(), v2 = arg1.getSize();
		return v1.compareTo(v2);
	}

}
