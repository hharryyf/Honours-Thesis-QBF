package qbfefficient;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import qbfexpression.Conflict;
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
	public TwoWatchedLiteralFormula(int n) {
		this.assign = new AssignmentStack();
		this.quantifier = new QuantifierPrefixVSIDS(n);
		this.original = new TwoWatchedLiteralStack(n, this);
		this.lemma = new TwoWatchedLiteralStack(n, this);
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
		this.assign.assign(v, 'N', -1);
		this.quantifier.remove(v);
		this.original.set(v);
	}
	
	@Override
	public int depth(int v) {
		if (v < 0) v = -v;
		return this.quantifier.depth[v];
	}
	
	@Override
	public void undo() {
		while (!this.assign.literal.isEmpty() && this.assign.peek().second.first != 'N') {
			Pair<Integer, Pair<Character, Integer>> pair = this.assign.unassign();
			this.quantifier.insert(pair.first);
			this.original.unassign(pair.first);
			this.lemma.unassign(pair.first);
		}
		
		if (!this.assign.literal.isEmpty()) {
			Pair<Integer, Pair<Character, Integer>> pair = this.assign.unassign();
			this.quantifier.insert(pair.first);
			this.original.unassign(pair.first);
			this.lemma.unassign(pair.first);
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
				this.original.unit.remove(entry.getKey());
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
	public Conflict getReason() {
		if (this.lemma.evaluate() == 0) return this.lemma.getConflict();
		return this.original.getConflict();
	}
}
