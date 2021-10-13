package qbfefficient;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import qbfexpression.Quantifier;
import utilstructure.Pair;

/*
 * Two watched literal data structure for QBF
 * */
public class TwoWatchedLiteralFormula implements EfficientQBFFormula {
	protected AssignmentStack assign;
	protected QuantifierPrefixVSIDS quantifier;
	private TwoWatchedLiteralStack original, lemma;
	private List<Quantifier> qlist;
	private Set<Integer> permanantUnit;
	private boolean locked = false;
	public static enum Method {
		BT, BJ, CDCLSBJ, QCDCL
	}
	// static command-line-argument region
	public static int maxclause = 2500, maxcube = 2500;
	public static long setcount = 0, clause_iter = 0;
	public static boolean timer = true;
	public static Method solvertype = Method.BJ;
	public TwoWatchedLiteralFormula(int n) {
		this.assign = new AssignmentStack();
		this.quantifier = new QuantifierPrefixVSIDS(n);
		this.original = new TwoWatchedLiteralClauseStack(n, this);
		this.lemma = new TwoWatchedLiteralClauseStack(n, this);
		this.permanantUnit = new TreeSet<>();
		this.qlist = new ArrayList<>();
	}
	
	@Override
	public void addQuantifier(Quantifier q) {
		this.qlist.add(q);
		if (this.qlist.size() == this.quantifier.quantifier.length - 1) this.normalize(0);
	}
	
	@Override
	public void addClause(List<Integer> c) {
		if (locked) MyError.abort("cannot insert clause after normalized, call learn instead");
		ArrayList<Pair<Integer, Integer>> curr= new ArrayList<>();
		ArrayList<Integer> list = new ArrayList<>();
		for (Integer v : c) {
			curr.add(new Pair<>(this.quantifier.depth[Math.abs(v)], v));
		}
		
		Collections.sort(curr);
		while (!isMax(curr.get(curr.size() - 1).second)) {
			curr.remove(curr.size() - 1);
		}
	    
		if (curr.isEmpty()) {
			MyError.abort("try to insert empty clause!\nUNSAT\n");
		}
		
		if (curr.size() == 1) {
			this.permanantUnit.add(curr.get(0).second);
			return;
		}
		
		for (Pair<Integer, Integer> v : curr) list.add(v.second); 
		this.original.addClause(list);
	}
	
	@Override
	public void learn(List<Integer> c) {
		
	}
	
	@Override
	public void set(int v) {
		if (this.assign.hasVar(v)) return;
		if (TwoWatchedLiteralFormula.timer) TwoWatchedLiteralFormula.setcount += 1;
		this.assign.assign(v, 'N', -1);
		this.quantifier.remove(v);
		this.original.set(v);
		this.lemma.set(v);
	}
	
	@Override
	public int depth(int v) {
		if (v < 0) v = -v;
		return this.quantifier.depth[v];
	}
	
	private void undoBJ(ConflictBJ reason) {
		while (!this.assign.literal.isEmpty() && this.assign.peek().second.first != 'N') {
			Pair<Integer, Pair<Character, Integer>> pair = this.assign.unassign();
			if (!reason.isSolution()) {
				if (reason.contains(pair.first)) {
					ConflictSolution other = new ConflictBJ(false);
					if (pair.second.second == -1) {
						reason.drop(null, pair.first);
					} else {
						other.addLiteral(this, this.original.formula.get(pair.second.second));
					    reason.resolve(other, pair.first, this);
					}
				}
			}
			this.quantifier.insert(pair.first);
			this.original.unassign(pair.first);
		}
		
		if (!this.assign.literal.isEmpty()) {
			Pair<Integer, Pair<Character, Integer>> pair = this.assign.unassign();
			this.quantifier.insert(pair.first);
			this.original.unassign(pair.first);
		}
	}
	
	@Override
	public void undo(ConflictSolution reason) {
	    if (TwoWatchedLiteralFormula.solvertype == Method.BT) {
	    	while (!this.assign.literal.isEmpty() && this.assign.peek().second.first != 'N') {
				Pair<Integer, Pair<Character, Integer>> pair = this.assign.unassign();
				this.quantifier.insert(pair.first);
				this.original.unassign(pair.first);
			}
			
			if (!this.assign.literal.isEmpty()) {
				Pair<Integer, Pair<Character, Integer>> pair = this.assign.unassign();
				this.quantifier.insert(pair.first);
				this.original.unassign(pair.first);
			}
	    } else if (TwoWatchedLiteralFormula.solvertype == Method.BJ) {
	    	if (reason == null) MyError.abort("null reason for backjumping solver");
			undoBJ((ConflictBJ) reason);
		} else {
			
		}
	}
	
	@Override
	public int evaluate() {
		int v1 = this.original.evaluate(), v2 = this.lemma.evaluate();
		if (v1 == 0 || v2 == 0) return 0;
		if (v1 == 1 && v2 == 1) return 1;
		return -1;
	}
	
	@Override
	public void simplify() {
		for (Integer v : this.permanantUnit) {
			if (evaluate() != -1) break;
			if (this.assign.hasVar(v)) continue;
			propagate(v, 'U', -1);
		}
		
		while ((!this.original.unit.isEmpty() || !this.lemma.unit.isEmpty()) && evaluate() == -1) {
			Map.Entry<Integer, Integer> entry = null;
			if (!this.original.unit.isEmpty()) {
				entry = this.original.unit.firstEntry();
				propagate(entry.getKey(), 'U', entry.getValue());
				this.original.unit.remove(entry.getKey());
			} else {
				entry = this.lemma.unit.firstEntry();
				propagate(entry.getKey(), 'E', entry.getValue());
				this.lemma.unit.remove(entry.getKey());
			}
		}
		
		
		this.original.unit.clear();
		this.lemma.unit.clear();
	}
	
	private void propagate(int v, char type, int id) {
		if (this.assign.hasLiteral(v)) {
			return;
		}
		
		if (this.assign.hasLiteral(-v)) {
			this.original.contradict.add(id);
			return;
		}
		if (TwoWatchedLiteralFormula.timer) TwoWatchedLiteralFormula.setcount += 1;
		this.assign.assign(v, type, id);
		this.quantifier.remove(v);
		this.original.set(v);
	}
	
	@Override
	public Quantifier peek() {
		if (!locked) MyError.abort("formula not normalized");
		return this.quantifier.peek();
	}
	
	@Override
	public boolean isMax(int v) {
		if (v < 0) v = -v;
		return this.quantifier.quantifier[v].isMax();
	}
	
	@Override
	public void normalize(int type) {
		// type = 0 means normalize the quantifier
		if (type == 0) {
			int d = 1, i;
			for (i = 0 ; i < this.qlist.size(); ++i) {
				if (i == 0) {
					this.quantifier.insert(this.qlist.get(i), d);
				} else {
					if (this.qlist.get(i).isMax() != this.qlist.get(i-1).isMax()) {
						d++;
					}
					this.quantifier.insert(this.qlist.get(i), d);
				}
			}
		} else if (type == 1) {
			// init the watched literal data structure and quantifier blocks
			// no void quantifier, unit literal exists at this point
			for (int i = 0 ; i < this.quantifier.quantifier.length; ++i) this.quantifier.score[i] = 0.0;
			for (int i = 0 ; i < this.original.formula.size(); ++i) {
				for (Integer v : this.original.formula.get(i).existential) {
					this.quantifier.score[Math.abs(v)] += 1.0;
				}
                
				for (Integer v : this.original.formula.get(i).universal) {
					this.quantifier.score[Math.abs(v)] += 1.0;
				}
			}
			this.quantifier.normalized();
			this.original.init();
			this.locked = true;
		} else {
			// TODO, things to do during restart
		}
	} 
	
	@Override
	public ConflictSolution getReason() {
		if (evaluate() == 1) {
			return this.original.getSolution();
		} else {
			return this.original.getConflict();
		}
	}

	@Override
	public boolean isassigned(int v) {
		return this.assign.hasVar(v);
	}

	@Override
	public TwoWatchedLiteralClause unitId(int v) {
		// TODO Auto-generated method stub
		Pair<Character, Integer> cid = this.assign.getUnit(v);
		if (cid.first == 'U') return this.original.formula.get(cid.second);
		if (cid.first == 'E') return this.lemma.formula.get(cid.second);
		return null;
	}
}
