package qbfefficient;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

import utilstructure.Pair;


public class TwoWatchedLiteralClauseStack extends TwoWatchedLiteralStack {
	private String lm = new String("2_WL_CLAUSE_STACK");
	private int n;
	private boolean PLE = false;
	private List<HashSet<Integer>> watcher;
	protected TreeSet<Integer> pure;
	public TwoWatchedLiteralClauseStack(int n, TwoWatchedLiteralFormula f, int dim, boolean PLE) {
		this.n = n;
		this.counter = new SatisfiedCounter();
		this.counter.setDim(dim);
		this.formula = new ArrayList<>();
		this.unit = new TreeMap<>();
		this.contradict = new TreeSet<>();
		this.conflictunit = new TreeSet<>();
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
		this.PLE = PLE;
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
		List<Integer> list = new ArrayList<>();
		if (v > 0) {
			for (Integer w : this.varPosToid.get(v)) {
				if (this.counter.addsat(w) && this.PLE) list.add(w); 
			}	
		} else {
			for (Integer w : this.varNegToid.get(-v)) {
				if (this.counter.addsat(w) && this.PLE) list.add(w);
			}
		}
		// System.out.println("set " + v);
		if (this.counter.getDim() == 0) MyLog.log(lm, 3, "Assign", v);
		twowatchedassign(v);
		if (this.PLE && evaluate() == -1) {
			twoclauseadjust(list);
		}
	}
	
	
	private void twoclauseadjust(List<Integer> candidate) {
		for (Integer clauseid : candidate) {
			Iterator<Integer> iter = this.watcher.get(clauseid).iterator();
			while (iter.hasNext()) {
				// these are the literals that are watching the current clause
				int literal = iter.next();
				boolean found = false;
				if (f.isassigned(literal) || this.pure.contains(-literal) || (literal > 0 && this.pure.contains(literal))) continue;
				if (literal > 0) {
					for (Integer id : this.varPosToid.get(literal)) {
						if (!this.counter.issat(id)) {
							iter.remove();
							this.watcher.get(id).add(literal);
							found = true;
							break;
						}
					}
				} else {
					for (Integer id : this.varNegToid.get(-literal)) {
						if (!this.counter.issat(id)) {
							iter.remove();
							this.watcher.get(id).add(literal);
							found = true;
							break;
						}
					}
				}
				
				if (!found) addPure(-literal);
			}
		}
	}
	
	private void addPure(int literal) {
		MyLog.log(lm, 3, "Find PL", literal);
		this.pure.add(literal);
	}
	
	
	@Override
	public void init() {
		int i, j;
		
		if (this.PLE) {
			this.pure = new TreeSet<>();
			this.watcher = new ArrayList<>();
		}
		
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
			
			if (this.PLE) {
				this.watcher.add(new HashSet<>());
			}
		}
		
		if (this.PLE) {
			for (i = 1 ; i <= n; ++i) {
				int posid = this.varPosToid.get(i).get(0);
				int negid = this.varNegToid.get(i).get(0);
				this.watcher.get(posid).add(i);
				this.watcher.get(negid).add(-i);
			}
		}
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
		
		if (literalid == -1) MyLog.log(lm, 0, "watched invalid literal");
		
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
		if (f.isMax(v)) MyLog.log(lm, 0, "invalid call to adjustTwoWatchUniversal, v is existential");
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
			if (wr.watchedE.isEmpty()) {
				System.out.println(this.f.assign.assignment);
				System.out.println(wr);
			}
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
		if (!f.isMax(v)) MyLog.log(lm, 0, "invalid call to adjustTwoWatchExistential, v is universal");
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
				
				if (wr.watchedU.isEmpty()) MyLog.log(lm, 0, "invariant broken in assignE, no universal watched");
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
		// System.out.println("unset " + v);
		if (this.counter.getDim() == 0) MyLog.log(lm, 3, "Unassign", v);
		if (v > 0) {
			for (Integer id : this.varPosToid.get(v)) {
				if (this.counter.getDim() == 1) {
					MyLog.log(lm, 2, "Unassign " + v + " clause id " + id + " content: " + this.formula.get(id));
				}
				this.counter.removesat(id);
			}
		} else {
			for (Integer id : this.varNegToid.get(-v)) {
				if (this.counter.getDim() == 1) {
					MyLog.log(lm, 2, "Unassign " + v + " clause id " + id + " content: " + this.formula.get(id));
				}
				this.counter.removesat(id);
			}
		}
		
		if (TwoWatchedLiteralFormula.depend) {
			for (Pair<Integer, Integer> iter : f.dependgraph.get(-v + f.varsize)) {
				f.tempunit.remove(iter);
			}
			f.dependgraph.get(-v + f.varsize).clear();
		}
	}
	
	private void addUnit(int v, int fid) {
		this.unit.put(v, fid);
	}
	
	@Override
	public int evaluate() {
		if (this.counter.satClause() == this.formula.size()) return 1;
		if (!this.contradict.isEmpty() || !this.conflictunit.isEmpty()) return 0;
		return -1;
	}
	
	@Override
	public ConflictSolution getConflict() {
		if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BT) {
			ConflictSolution ret = new ConflictBJ(false);
			this.contradict.clear();
			return ret;
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BJ
				|| TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PBJ) {
			// learning strategy is Backjumping
			// get the clause corresponds to the conflict
			TwoWatchedLiteralClause C = this.formula.get(contradict.first());
			ConflictSolution ret = new ConflictBJ(false);
			// and clear out the conflict
			this.contradict.clear();
			ret.addLiteral(this.f, C);
			return ret;
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.CDCLSBJ 
				|| TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.QCDCL
				|| TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PL) {
			ConflictSolution ret = null;
			if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.CDCLSBJ) {
				ret = new ConflictCDCLSBJ(false);
			} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.QCDCL) {
				ret = new ConflictSolutionQCDCL(false);
			} else {
				ret = new PNSLearnReason(false);
				((PNSLearnReason) ret).status = PNSLearnReason.Status.pending;
			}
			
			if (!this.contradict.isEmpty()) {
				TwoWatchedLiteralClause C = this.formula.get(contradict.first());
				// and clear out the conflict
				ret.addLiteral(this.f, C);
			} else if (!this.conflictunit.isEmpty()) {
				List<Integer> vc = new ArrayList<>();
				vc.add(this.conflictunit.first());
				ret.addAssignment(f, vc);
			}
			this.contradict.clear();
			this.conflictunit.clear();
			return ret;
		} 
		
		return null;
	}
	
	// v is the universal literal, 
	private boolean canremove(int v, Map<Integer, Integer> ass) {
		if (f.isMax(v)) MyLog.log(lm, 2, "canremove: v is existential, invariant broken");
		List<Integer> list = null;
		if (v < 0) {
			list = this.varNegToid.get(-v);
	    } else {
	    	list = this.varPosToid.get(v);
	    }
		
		for (Integer id : list) {
			boolean ok = false;
	    	for (Integer u : this.formula.get(id).existential) {
	    		if (ass.containsKey(u)) {
	    			ok = true;
	    			break;
	    		}
	    	}
	    	
	    	if (!ok) {
		    	for (Integer u : this.formula.get(id).universal) {
		    		if (ass.containsKey(u)) {
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
		
		if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BT) {
			ConflictSolution c = new ConflictBJ(true);
			return c;
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BJ || TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.CDCLSBJ
			|| TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PBJ) {
			// learning strategy is Backjumping
			HashMap<Integer, Integer> ass = new HashMap<>(f.assign.literal);
			int mx = -1;
			LinkedList<Integer> ret = new LinkedList<>();
			for (Pair<Integer, AssignId> p : f.assign.assignment) {
				if (!f.isMax(p.first)) {
					ret.addFirst(p.first);
					mx = Math.max(f.depth(p.first), mx);
				}
			}
			
			for (int i = 1; i <= n; ++i) {
				if (f.isMax(i) && f.depth(i) > mx && !ass.containsKey(-i) && !ass.containsKey(i)) ass.put(i, 0);
			}
			
			Iterator<Integer> iter = ret.iterator();
			while (iter.hasNext()) {
				int v = iter.next();
				ass.remove(v);
				if (canremove(v, ass)) {
					iter.remove();
				} else {
					ass.put(v, 0);
				}
			}
			
			ConflictSolution c = null;
			if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BJ
				|| TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PBJ) {
				c = new ConflictBJ(true);
			} else {
				c = new ConflictCDCLSBJ(true);
			}
			c.addAssignment(f, ret);
			return c;
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.QCDCL) {
			HashMap<Integer, Integer> ass = new HashMap<>(f.assign.literal);
			LinkedList<Integer> ret = new LinkedList<>();
			LinkedList<Integer> other = new LinkedList<>();
			int mx = -1;
			for (Pair<Integer, AssignId> p : f.assign.assignment) {
				if (!f.isMax(p.first)) {
					ret.addFirst(p.first);
					mx = Math.max(f.depth(p.first), mx);
				} else {
					other.add(p.first);
				}
			}
			
			Iterator<Integer> iter = ret.iterator();
			
			for (int i = 1; i <= n; ++i) {
				if (f.isMax(i) && f.depth(i) > mx && !ass.containsKey(-i) && !ass.containsKey(i)) ass.put(i, 0);
			}
			
			while (iter.hasNext()) {
				int v = iter.next();
				ass.remove(v);
				if (canremove(v, ass)) {
					iter.remove();
				} else {
					ass.put(v, 0);
				}
			}
			
			int mxlv = -1;
			for (Integer v : ret) {
				mxlv = Math.max(f.depth(v), mxlv);
			}
			
			for (Integer v : other) {
				if (f.depth(v) < mxlv) ret.add(v);
			}
			
			ConflictSolution c = new ConflictSolutionQCDCL(true);
			c.addAssignment(f, ret);
			MyLog.log(lm, 2, "model generation ", ret);
			return c;
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PL) {
			HashMap<Integer, Integer> ass = new HashMap<>(f.assign.literal);
			LinkedList<Integer> ret = new LinkedList<>();
			LinkedList<Integer> other = new LinkedList<>();
			int mx = -1;
			for (Pair<Integer, AssignId> p : f.assign.assignment) {
				if (!f.isMax(p.first)) {
					ret.addFirst(p.first);
					mx = Math.max(f.depth(p.first), mx);
				} else {
					other.add(p.first);
				}
			}
			
			Iterator<Integer> iter = ret.iterator();
			
			for (int i = 1; i <= n; ++i) {
				if (f.isMax(i) && f.depth(i) > mx && !ass.containsKey(-i) && !ass.containsKey(i)) ass.put(i, 0);
			}
			
			while (iter.hasNext()) {
				int v = iter.next();
				ass.remove(v);
				if (canremove(v, ass)) {
					iter.remove();
				} else {
					ass.put(v, 0);
				}
			}
			
			int mxlv = -1;
			for (Integer v : ret) {
				mxlv = Math.max(f.depth(v), mxlv);
			}
			
			for (Integer v : other) {
				if (f.depth(v) < mxlv) ret.add(v);
			}
			
			ConflictSolution c = new PNSLearnReason(true);
			((PNSLearnReason) c).status = PNSLearnReason.Status.pending;
			c.addAssignment(f, ret);
			MyLog.log(lm, 2, "model generation ", ret);
			return c;
		} 
		
		return null;
	}

	@Override
	public void learn(List<Integer> c) {
		TwoWatchedLiteralClause ret = new TwoWatchedLiteralClause();
		ret.setFormula(f);
		int mx = -1, l = -1, unass = -1, tol = 0;
		for (Integer v : c) {
			if (v > 0) {
				this.varPosToid.get(v).add(this.formula.size());
			} else {
				this.varNegToid.get(-v).add(this.formula.size());
			}
			ret.addLiteral(v);
			int level = f.decisionLevel(v);
			// System.out.println(v + " level= " + level);
			if (f.isassigned(v) && mx < level) {
				l = v;
				mx = level;
			}
			
			if (!f.isassigned(v)) {
				tol++;
				if (f.isMax(v)) {
					unass = v;
				}
				
				if (TwoWatchedLiteralFormula.vsids) {
					f.quantifier.updateWeight(Math.abs(v), f.quantifier.score[Math.abs(v)] + 2.0);
				}
			} else {
				if (TwoWatchedLiteralFormula.vsids) {
					f.quantifier.score[Math.abs(v)] += 2.0;
				}
			}
		}
		
		ret.setId(this.formula.size());
		this.formula.add(ret);
		MyLog.log(lm, 2, "learned ", ret);
		int i = this.formula.size() - 1, j, cnt = 0;
		for (j = 0 ; j < this.formula.get(i).existential.size() && cnt < 2; ++j) {
			int v = this.formula.get(i).existential.get(j);
			if ((v > 0 && Math.abs(v) == Math.abs(l)) || (v > 0 && !f.isassigned(v))) {
				this.watchedFormulaPos.get(v).put(i, j);
				this.formula.get(i).watchedE.add(j);
				++cnt;
			} else if ((v < 0 && Math.abs(v) == Math.abs(l)) || (v < 0 && !f.isassigned(v))) {
				this.watchedFormulaNeg.get(-v).put(i, j);
				this.formula.get(i).watchedE.add(j);
				++cnt;
			}
		}
		
		for (j = 0 ; j < this.formula.get(i).universal.size() && cnt < 2; ++j) {
			int v = this.formula.get(i).universal.get(j);
			if ((v > 0 && Math.abs(v) == Math.abs(l)) || (v > 0 && !f.isassigned(v))) {
				this.watchedFormulaPos.get(v).put(i, j);
				this.formula.get(i).watchedU.add(j);
				++cnt;
			} else if ((v < 0 && Math.abs(v) == Math.abs(l)) || (v < 0 && !f.isassigned(v))) {
				this.watchedFormulaNeg.get(-v).put(i, j);
				this.formula.get(i).watchedU.add(j);
				++cnt;
			}
			
		}
		
		
		
		if (TwoWatchedLiteralFormula.depend && tol == 1) {
			f.dependgraph.get(l + f.varsize).add(new Pair<>(unass, i));
			f.tempunit.add(new Pair<>(unass, i));
			if (!f.isMax(unass)) {
				MyLog.log(lm, 0, "we have a problem not UIP");
			}
		}
		
		
		
		if (this.formula.get(i).watchedE.isEmpty()) {
			MyLog.log(lm, 0, "fail to watch 2 literals: ", this.formula.get(i));
		}
		//System.out.println("another literal " + l + " learn clause " + ret);
	}
}
