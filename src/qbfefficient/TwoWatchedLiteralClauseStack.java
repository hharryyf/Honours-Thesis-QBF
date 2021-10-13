package qbfefficient;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import utilstructure.Pair;


public class TwoWatchedLiteralClauseStack extends TwoWatchedLiteralStack {
	public TwoWatchedLiteralClauseStack(int n, TwoWatchedLiteralFormula f) {
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
		this.f = f;
	}
	
	@Override
	public void addClause(List<Integer> c) {
		TwoWatchedLiteralClause ret = new TwoWatchedLiteralClause();
		ret.setFormula(f);
		for (Integer v : c) {
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
	
	@Override
	public void set(int v) {
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
		
		if (f.isMax(v)) {
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
		
		if (f.isMax(v)) {
			this.formula.get(clauseid).watchedE.remove(literalid);
		} else {
			this.formula.get(clauseid).watchedU.remove(literalid);
		}
	}
	
	private void twowatchedassign(int v) {
		if (v > 0) {
			Map<Integer, Integer> mp = this.watchedFormulaNeg.get(v);
			if (!f.isMax(v)) {
				adjustTwoWatchUniversal(v, mp);
			} else {
				adjustTwoWatchExistential(v, mp);
			}	
		} else {
			Map<Integer, Integer> mp = this.watchedFormulaPos.get(-v);
			if (!f.isMax(v)) {
				adjustTwoWatchUniversal(v, mp);
			} else {
				adjustTwoWatchExistential(v, mp);
			}
		}
	}
	
	/**
	 * 
	 * @param v :: literal assignment, must be universal literal
	 * @param watched, negation watched literals
	 * if v is positive, neg is passed in
	 * if v is negative, pos watched is passed in
	 */
	private void adjustTwoWatchUniversal(int v, Map<Integer, Integer> watched) {
		if (f.isMax(v)) MyError.abort("invalid call to adjustTwoWatchUniversal, v is existential");
		Iterator<Map.Entry<Integer, Integer>> iter = watched.entrySet().iterator();
		// entry key = clause id, entry value = watched literal id in the array (existential/universal)
		while (iter.hasNext()) {
			// iterate through the entry set
			Map.Entry<Integer, Integer> entry = iter.next();
			// rule number 0, if the clause is satisfied, skip
			if (this.counter.issat(entry.getKey())) continue;
			// iterate through the existential and see if we can watch one of it to watch
			// such that we watch two existential
			TwoWatchedLiteralFormula.clause_iter++;
			TwoWatchedLiteralClause wr = this.formula.get(entry.getKey());
			boolean found = false;
			for (int i = 0; i < wr.existential.size(); ++i) {
				// has found an unwatched existential literal
				if (!wr.watchedE.contains(i) && !f.assign.hasVar(wr.existential.get(i))) {
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
				if (!wr.watchedU.contains(i) && !f.assign.hasVar(wr.universal.get(i)) && f.depth(wr.universal.get(i)) < f.depth(existV)) {
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
			if (!found) this.addUnit(existV, entry.getKey().intValue());
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
		if (!f.isMax(v)) MyError.abort("invalid call to adjustTwoWatchExistential, v is universal");
		Iterator<Map.Entry<Integer, Integer>> iter = watched.entrySet().iterator();
		while (iter.hasNext()) {
			// again simple case, when the clause is satisfied, ignore it
			Map.Entry<Integer, Integer> entry = iter.next();
			if (this.counter.issat(entry.getKey())) continue;
			TwoWatchedLiteralFormula.clause_iter++;
			// the clause that contains this watched existential literal
			TwoWatchedLiteralClause wr = this.formula.get(entry.getKey());
			// if we are watching two existential literals
			if (wr.watchedE.size() == 2) {
				boolean found = false;
				// simpler case, find an existential to replace the watched literal
				for (int i = 0; i < wr.existential.size(); ++i) {
					// has found an unwatched existential literal
					if (!wr.watchedE.contains(i) && !this.f.assign.hasVar(wr.existential.get(i))) {
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
					if (!this.f.assign.hasVar(wr.universal.get(i)) && f.depth(wr.universal.get(i)) < f.depth(existV)) {
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
					if (!wr.watchedE.contains(i) && !this.f.assign.hasVar(wr.existential.get(i))) {
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
				if (f.depth(wr.existential.get(existV)) > f.depth(universeV)) {
					wr.watchedE.remove(entry.getValue());
					watch(wr.existential.get(existV), entry.getKey(), existV);
					iter.remove();
					continue;
				}
				
				// try to find the other watched literal, case we can find an existential
				for (int i = existV - 1; i >= 0; --i) {
					if (!wr.watchedE.contains(i) && !this.f.assign.hasVar(wr.existential.get(i))) {
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
					if (!this.f.assign.hasVar(wr.universal.get(i)) && f.depth(wr.universal.get(i)) < f.depth(wr.existential.get(existV))) {
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
	
	@Override
	public void unassign(int v) {
		if (v > 0) {
			for (Integer id : this.varPosToid.get(v)) {
				this.counter.removesat(id);
			}
		} else {
			for (Integer id : this.varNegToid.get(-v)) {
				this.counter.removesat(id);
			}
		}
	}
	
	private void addUnit(int v, int fid) {
		this.unit.put(v, fid);
	}
	
	@Override
	public int evaluate() {
		if (this.counter.satClause() == this.formula.size()) return 1;
		if (!this.contradict.isEmpty()) return 0;
		return -1;
	}
	
	@Override
	public void init() {
		int i, j;
		for (i = 0 ; i < this.formula.size(); ++i) {
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
	
	@Override
	public ConflictSolution getConflict() {
		if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BJ) {
			// learning strategy is Backjumping
			// get the clause corresponds to the conflict
			TwoWatchedLiteralClause C = this.formula.get(contradict.first());
			ConflictSolution ret = new ConflictBJ(false);
			// and clear out the conflict
			this.contradict.clear();
			ret.addLiteral(this.f, C);
			return ret;
		}
		
		return null;
	}
	
	// v is the universal literal, 
	private boolean canremove(int v, Set<Integer> ass) {
		if (f.isMax(v)) MyError.abort("canremove: v is existential, invariant broken");
		List<Integer> list = null;
		if (v < 0) {
			list = this.varNegToid.get(-v);
	    } else {
	    	list = this.varPosToid.get(v);
	    }
		
		for (Integer id : list) {
			boolean ok = false;
	    	for (Integer u : this.formula.get(id).existential) {
	    		if (ass.contains(u)) {
	    			ok = true;
	    			break;
	    		}
	    	}
	    	
	    	if (!ok) {
		    	for (Integer u : this.formula.get(id).universal) {
		    		if (ass.contains(u)) {
		    			ok = true;
		    			break;
		    		}
		    	}
	    	}
	    	
	    	if (!ok) {
	    		return false;
	    	}
	    }
		
		return true;
	}
	
	@Override
	public ConflictSolution getSolution() {
		if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BJ) {
			// learning strategy is Backjumping
			HashSet<Integer> ass = new HashSet<>(f.assign.literal);
			LinkedList<Integer> ret = new LinkedList<>();
			for (Pair<Integer, Pair<Character, Integer>> p : f.assign.assignment) {
				if (!f.isMax(p.first)) {
					ret.addFirst(p.first);
				}
			}
			
			Iterator<Integer> iter = ret.iterator();
			while (iter.hasNext()) {
				int v = iter.next();
				ass.remove(v);
				if (canremove(v, ass)) {
					iter.remove();
				} else {
					ass.add(v);
				}
			}
			
			ConflictSolution c = new ConflictBJ(true);
			c.addAssignment(f, ret);
			return c;
		}
		
		return null;
	}
}
