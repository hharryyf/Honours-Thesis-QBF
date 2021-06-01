package qbfsolver;

import qbfexpression.CnfExpression;

public interface Solver {
	boolean solve(CnfExpression f);
}
