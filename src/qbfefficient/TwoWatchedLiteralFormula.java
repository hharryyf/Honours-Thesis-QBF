package qbfefficient;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import qbfexpression.Conflict;
import qbfexpression.Quantifier;
import utilstructure.Pair;

/*
 * Two watched literal data structure for QBF
 * */
public class TwoWatchedLiteralFormula {
	protected AssignmentStack assign;
	protected QuantifierPrefixVSIDS quantifier;
	protected List<TwoWatchedLiteralClause> formula;
	protected List<List<Integer>> varNegToid, varPosToid;
	protected SatisfiedCounter counter;
	protected List<Map<Integer, Integer>> watchedFormulaPos;
	protected List<Map<Integer, Integer>> watchedFormulaNeg;
	protected TreeMap<Integer, Integer> unit;
	protected TreeSet<Integer> contradict;
	private List<Quantifier> qlist;
	private Set<Integer> permanantUnit;
	public TwoWatchedLiteralFormula(int n) {
		this.assign = new AssignmentStack();
		this.quantifier = new QuantifierPrefixVSIDS(n);
		this.counter = new SatisfiedCounter();
		this.formula = new ArrayList<>();
		this.unit = new TreeMap<>();
		this.contradict = new TreeSet<>();
		this.varNegToid = new ArrayList<>();
		this.varPosToid = new ArrayList<>();
		this.watchedFormulaPos = new ArrayList<>();
		this.watchedFormulaNeg = new ArrayList<>();
		// can be changed
		this.permanantUnit = new TreeSet<>();
		for (int i = 0 ; i <= n; ++i) {
			this.varNegToid.add(new ArrayList<>());
			this.varPosToid.add(new ArrayList<>());
			this.watchedFormulaPos.add(new TreeMap<>());
			this.watchedFormulaNeg.add(new TreeMap<>());
		}
		
		this.qlist = new ArrayList<>();
	}
	
	public void addQuantifier(Quantifier q) {
		this.qlist.add(q);
		if (this.qlist.size() == this.quantifier.quantifier.length - 1) this.normalize(0);
	}
	
	public void addClause(List<Integer> c) {
		ArrayList<Pair<Integer, Integer>> curr= new ArrayList<>();
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
		
		TwoWatchedLiteralClause ret = new TwoWatchedLiteralClause();
		ret.setFormula(this);
		for (Pair<Integer, Integer> p : curr) {
			int v = p.second;
			if (v > 0) {
				this.varPosToid.get(v).add(this.formula.size());
			} else {
				this.varNegToid.get(-v).add(this.formula.size());
			}
			ret.addLiteral(v);
		}
		
		ret.setId(this.formula.size());
		this.formula.add(ret);
	}
	
	public void learn(List<Integer> c) {
		
	}
	
	public void set(int v) {
		if (this.assign.hasVar(v)) return;
		this.assign.assign(v, 'N', -1);
		this.quantifier.remove(v);
		if (v > 0) {
			for (Integer w : this.varPosToid.get(v)) {
				this.counter.addsat(w);
			}	
		} else {
			for (Integer w : this.varNegToid.get(-v)) {
				this.counter.addsat(w);
			}
		}
		
		twowatchedassign(v);
	}
	
	public void propagate(int v, int id) {
		if (this.assign.hasLiteral(v)) {
			return;
		}
		
		if (this.assign.hasLiteral(-v)) {
			this.contradict.add(id);
			return;
		}
		
		this.assign.assign(v, 'U', id);
		this.quantifier.remove(v);
		if (v > 0) {
			for (Integer w : this.varPosToid.get(v)) {
				this.counter.addsat(w);
			}	
		} else {
			for (Integer w : this.varNegToid.get(-v)) {
				this.counter.addsat(w);
			}
		}
		
		twowatchedassign(v);
	}
	
	private void watch(int v, int clauseid, int literalid) {
		if (v > 0) {
			this.watchedFormulaPos.get(v).put(clauseid, literalid);
		} else {
			this.watchedFormulaNeg.get(-v).put(clauseid, literalid);
		}
		
		if (isMax(v)) {
			this.formula.get(clauseid).watchedE.add(literalid);
		} else {
			this.formula.get(clauseid).watchedU.add(literalid);
		}
	}
	
	private void unwatch(int v, int clauseid) {
		int literalid = -1;
		if (v > 0) {
			literalid = this.watchedFormulaPos.get(v).get(clauseid);
			this.watchedFormulaPos.get(v).remove(clauseid);
		} else {
			literalid = this.watchedFormulaNeg.get(-v).get(clauseid);
			this.watchedFormulaNeg.get(-v).remove(clauseid);
		}
		
		if (literalid == -1) MyError.abort("watched invalid literal");
		
		if (isMax(v)) {
			this.formula.get(clauseid).watchedE.remove(literalid);
		} else {
			this.formula.get(clauseid).watchedU.remove(literalid);
		}
	}
	
	private int depth(int v) {
		if (v < 0) v = -v;
		return this.quantifier.depth[v];
	}
	/**
	 * 
	 * @param v :: literal assignment, must be universal literal
	 * @param watched, negation watched literals
	 * if v is positive, neg is passed in
	 * if v is negative, pos watched is passed in
	 */
	private void adjustTwoWatchUniversal(int v, Map<Integer, Integer> watched) {
		if (isMax(v)) MyError.abort("invalid call to adjustTwoWatchUniversal, v is existential");
		Iterator<Map.Entry<Integer, Integer>> iter = watched.entrySet().iterator();
		// entry key = clause id, entry value = watched literal id in the array (existential/universal)
		while (iter.hasNext()) {
			// iterate through the entry set
			Map.Entry<Integer, Integer> entry = iter.next();
			// rule number 0, if the clause is satisfied, skip
			if (this.counter.issat(entry.getKey())) continue;
			// iterate through the existential and see if we can watch one of it to watch
			// such that we watch two existential
			TwoWatchedLiteralClause wr = this.formula.get(entry.getKey());
			boolean found = false;
			for (int i = 0; i < wr.existential.size(); ++i) {
				// has found an unwatched existential literal
				if (!wr.watchedE.contains(i) && !this.assign.hasVar(wr.existential.get(i))) {
					watch(wr.existential.get(i), entry.getKey(), i);
					found = true;
					break;
				}
			}
			
			if (found) {
				wr.watchedU.remove(entry.getValue());
				iter.remove();
				continue;
			}
			
			//System.out.println(this.assign.assignment);
			//System.out.println("clause " + entry.getKey() + " " + wr.existential + " " + wr.universal);
			// if we fail to find one, we must find a universal that is outside the watched existential
			int existV = wr.existential.get(wr.watchedE.first());
			for (int i = 0; i < wr.universal.size(); ++i) {
				// has found an unwatched existential literal
				if (!wr.watchedU.contains(i) && !this.assign.hasVar(wr.universal.get(i)) && depth(wr.universal.get(i)) < depth(existV)) {
					// watch it
					watch(wr.universal.get(i), entry.getKey(), i);
					found = true;
					break;
				}
			}
			
			if (found) {
				// we can saftely unwatch the current universal literal
				wr.watchedU.remove(entry.getValue());
				iter.remove();
				continue;
			}
			
			// if both steps fail, we know existV is unit literal
			if (!found) this.addUnit(existV, entry.getKey());
		}
	}
	
	/**
	 * 
	 * @param v :: literal assignment, must be existential literal
	 * @param watched, negation watched literals
	 * if v is positive, neg is passed in
	 * if v is negative, pos watched is passed in
	 */
	private void adjustTwoWatchExistential(int v, Map<Integer, Integer> watched) {
		if (!isMax(v)) MyError.abort("invalid call to adjustTwoWatchExistential, v is universal");
		Iterator<Map.Entry<Integer, Integer>> iter = watched.entrySet().iterator();
		while (iter.hasNext()) {
			// again simple case, when the clause is satisfied, ignore it
			Map.Entry<Integer, Integer> entry = iter.next();
			if (this.counter.issat(entry.getKey())) continue;
			// the clause that contains this watched existential literal
			TwoWatchedLiteralClause wr = this.formula.get(entry.getKey());
			// if we are watching two existential literals
			if (wr.watchedE.size() == 2) {
				boolean found = false;
				// simpler case, find an existential to replace the watched literal
				for (int i = 0; i < wr.existential.size(); ++i) {
					// has found an unwatched existential literal
					if (!wr.watchedE.contains(i) && !this.assign.hasVar(wr.existential.get(i))) {
						watch(wr.existential.get(i), entry.getKey(), i);
						found = true;
						break;
					}
				}

				if (found) {
					wr.watchedE.remove(entry.getValue());
					iter.remove();
					continue;
				}
				
				// complicated case, we must find a universal that is outer of e_other
				// existV is the e_other described in the paper
				int existV = wr.existential.get(wr.watchedE.first());
				if (existV == -v) existV = wr.existential.get(wr.watchedE.last());
				for (int i = 0; i < wr.universal.size(); ++i) {
					// has found an unwatched existential literal, watch it
					if (!this.assign.hasVar(wr.universal.get(i)) && depth(wr.universal.get(i)) < depth(existV)) {
						watch(wr.universal.get(i), entry.getKey(), i);
						found = true;
						break;
					}
				}
				
				if (found) {
					// we can safely unwatch the current existential literal
					wr.watchedE.remove(entry.getValue());
					iter.remove();
					continue;
				}
				// otherwise, e_other is unit
				if (!found) this.addUnit(existV, entry.getKey());
			} else {
				// if we watch 1 existential and 1 universal
				// we do the following, try to find the two literals such that
				// either 2 existential or 1 existential and 1 universal such that depth(e) > depth(u)
				// if we fail to find 1 existential, we find a contradictory clause
				
				int existV = -1, existO = -1;
				for (int i = wr.existential.size() - 1; i >= 0; --i) {
					// has found an unwatched existential, unassigned literal
					if (!wr.watchedE.contains(i) && !this.assign.hasVar(wr.existential.get(i))) {
						existV = i;
						break;
					}
				}
				
				// contradictory case, no unassigned existential
				if (existV == -1) {
					this.contradict.add(entry.getKey());
					break;
				}
				
				if (wr.watchedU.isEmpty()) MyError.abort("invariant broken in assignE, no universal watched");
				int universeV = wr.universal.get(wr.watchedU.first());
				// if existV is already outside universalV, just unwatch e and watch existV
				if (depth(wr.existential.get(existV)) > depth(universeV)) {
					wr.watchedE.remove(entry.getValue());
					watch(wr.existential.get(existV), entry.getKey(), existV);
					iter.remove();
					continue;
				}
				
				// try to find the other watched literal, case we can find an existential
				for (int i = existV - 1; i >= 0; --i) {
					if (!wr.watchedE.contains(i) && !this.assign.hasVar(wr.existential.get(i))) {
						existO = i;
						break;
					}
				}
				
				// we find two existentials to substitute
				if (existO != -1) {
					watch(wr.existential.get(existO), entry.getKey(), existO);
					watch(wr.existential.get(existV), entry.getKey(), existV);
					wr.watchedE.remove(entry.getValue());
					this.unwatch(universeV, entry.getKey());
					iter.remove();
					continue;
				}
				
				// if we find 1 existential and 1 universal
				boolean found = false;
				for (int i = wr.universal.size() - 1; i >= 0; --i) {
					if (!this.assign.hasVar(wr.universal.get(i)) && depth(wr.universal.get(i)) < depth(wr.existential.get(existV))) {
						this.unwatch(universeV, entry.getKey());
						watch(wr.universal.get(i), entry.getKey(), i);
						found = true;
						break;
					}
				}
				
				if (found) {
					watch(wr.existential.get(existV), entry.getKey(), existV);
					wr.watchedE.remove(entry.getValue());
					iter.remove();
				} else {
					this.addUnit(wr.existential.get(existV), entry.getKey());
				}
			}
		}
	}
	
	private void twowatchedassign(int v) {
		if (v > 0) {
			Map<Integer, Integer> mp = this.watchedFormulaNeg.get(v);
			if (!isMax(v)) {
				adjustTwoWatchUniversal(v, mp);
			} else {
				adjustTwoWatchExistential(v, mp);
			}	
		} else {
			Map<Integer, Integer> mp = this.watchedFormulaPos.get(-v);
			if (!isMax(v)) {
				adjustTwoWatchUniversal(v, mp);
			} else {
				adjustTwoWatchExistential(v, mp);
			}
		}
	}
	
	public void undo() {
		while (!this.assign.literal.isEmpty() && this.assign.peek().second.first != 'N') {
			Pair<Integer, Pair<Character, Integer>> pair = this.assign.unassign();
			this.quantifier.insert(pair.first);
			if (pair.first > 0) {
				for (Integer id : this.varPosToid.get(pair.first)) {
					this.counter.removesat(id);
				}
			} else {
				for (Integer id : this.varNegToid.get(-pair.first)) {
					this.counter.removesat(id);
				}
			}
		}
		
		Pair<Integer, Pair<Character, Integer>> pair = this.assign.unassign();
		this.quantifier.insert(pair.first);
		if (pair.first > 0) {
			for (Integer id : this.varPosToid.get(pair.first)) {
				this.counter.removesat(id);
			}
		} else {
			for (Integer id : this.varNegToid.get(-pair.first)) {
				this.counter.removesat(id);
			}
		}
	}
	
	public int evaluate() {
		if (this.counter.satClause() == this.formula.size()) return 1;
		if (!this.contradict.isEmpty()) return 0;
		return -1;
	}
	
	public void unitpropagation() {
		for (Integer v : this.permanantUnit) {
			if (evaluate() != -1) break;
			if (this.assign.hasVar(v)) continue;
			propagate(v, -1);
		}
		
		while (!unit.isEmpty() && evaluate() == -1) {
			Map.Entry<Integer, Integer> entry = unit.firstEntry();
			propagate(entry.getKey(), entry.getValue());
			unit.remove(entry.getKey());
		}
		
		this.unit.clear();
	}
	
	public void addUnit(int v, int fid) {
		this.unit.put(v, fid);
	}
	
	public Quantifier peek() {
		return this.quantifier.peek();
	}
	
	public boolean isMax(int v) {
		if (v < 0) v = -v;
		return this.quantifier.quantifier[v].isMax();
	}
	
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
		} else {
			int i, j;
			for (i = 0 ; i < formula.size(); ++i) {
				for (Integer v : this.formula.get(i).existential) {
					this.quantifier.score[Math.abs(v)] += 1.0;
				}
                
				for (Integer v : this.formula.get(i).universal) {
					this.quantifier.score[Math.abs(v)] += 1.0;
				}
			}
			
			this.quantifier.normalized();
			
			for (i = 0 ; i < formula.size(); ++i) {
				int cnt = 0;
				for (j = 0 ; j < this.formula.get(i).existential.size() && cnt < 2; ++j, ++cnt) {
					int v = this.formula.get(i).existential.get(j);
					if (v > 0) {
						this.watchedFormulaPos.get(v).put(i, j);
					} else {
						this.watchedFormulaNeg.get(-v).put(i, j);
					}
					this.formula.get(i).watchedE.add(j);
				}
				
				for (j = 0 ; j < this.formula.get(i).universal.size() && cnt < 2; ++j, ++cnt) {
					int v = this.formula.get(i).universal.get(j);
					if (v > 0) {
						this.watchedFormulaPos.get(v).put(i, j);
					} else {
						this.watchedFormulaNeg.get(-v).put(i, j);
					}
					this.formula.get(i).watchedU.add(j);
				}
				
			}
		}
	} 
	
	public Conflict getReason() {
		this.contradict.clear();
		return null;
	}
}
