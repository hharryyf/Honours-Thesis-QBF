package qbfefficient;

import java.util.ArrayList;
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;

public class TwoWatchedLiteralCubeStack extends TwoWatchedLiteralStack {
	public TwoWatchedLiteralCubeStack(int n, TwoWatchedLiteralFormula twoWatchedLiteralFormula) {
		this.counter = new SatisfiedCounter();
		this.formula = new ArrayList<>();
		this.unit = new TreeMap<>();
		this.contradict = new TreeSet<>();
		this.varNegToid = new ArrayList<>();
		this.varPosToid = new ArrayList<>();
		this.watchedFormulaPos = new ArrayList<>();
		this.watchedFormulaNeg = new ArrayList<>();
		for (int i = 0 ; i <= n; ++i) {
			this.varNegToid.add(new ArrayList<>());
			this.varPosToid.add(new ArrayList<>());
			this.watchedFormulaPos.add(new TreeMap<>());
			this.watchedFormulaNeg.add(new TreeMap<>());
		}
		this.f = twoWatchedLiteralFormula;
	}

	@Override
	public void addClause(List<Integer> c) {
		// TODO Auto-generated method stub

	}

	@Override
	public void set(int v) {
		// TODO Auto-generated method stub

	}

	@Override
	public void unassign(int v) {
		// TODO Auto-generated method stub

	}

	@Override
	public int evaluate() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub

	}

	@Override
	public ConflictSolution getConflict() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ConflictSolution getSolution() {
		// TODO Auto-generated method stub
		return null;
	}

}
