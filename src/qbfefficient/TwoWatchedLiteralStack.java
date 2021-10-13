package qbfefficient;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

public abstract class TwoWatchedLiteralStack {
	protected List<TwoWatchedLiteralClause> formula;
	protected List<List<Integer>> varNegToid, varPosToid;
	protected SatisfiedCounter counter;
	protected List<Map<Integer, Integer>> watchedFormulaPos;
	protected List<Map<Integer, Integer>> watchedFormulaNeg;
	protected TreeMap<Integer, Integer> unit;
	protected TreeSet<Integer> contradict;
	protected TwoWatchedLiteralFormula f;
	public abstract void addClause(List<Integer> c);
	public abstract void set(int v);
	public abstract void unassign(int v);
	public abstract int evaluate();
	public abstract void init();
	public abstract ConflictSolution getConflict();
	public abstract ConflictSolution getSolution();
}
