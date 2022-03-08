package qbfefficient;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

import utilstructure.Pair;

public class TwoWatchedLiteralCubeStack extends TwoWatchedLiteralStack {
	private String lm = new String("2_WL_CUBE_STACK");
	public TwoWatchedLiteralCubeStack(int n, TwoWatchedLiteralFormula f, int dim) {
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
			for (Integer w : this.varNegToid.get(v)) {
				this.counter.addsat(w);
			}	
		} else {
			for (Integer w : this.varPosToid.get(-v)) {
				this.counter.addsat(w);
			}
		}
		// System.out.println("set " + v);
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
		
		if (literalid == -1) MyLog.log(lm, 0, "watched invalid literal");
		
		if (f.isMax(v)) {
			this.formula.get(clauseid).watchedE.remove(literalid);
		} else {
			this.formula.get(clauseid).watchedU.remove(literalid);
		}
	}
	
	private void twowatchedassign(int v) {
		if (v > 0) {
			Map<Integer, Integer> mp = this.watchedFormulaPos.get(v);
			if (!f.isMax(v)) {
				adjustTwoWatchUniversal(v, mp);
			} else {
				adjustTwoWatchExistential(v, mp);
			}	
		} else {
			Map<Integer, Integer> mp = this.watchedFormulaNeg.get(-v);
			if (!f.isMax(v)) {
				adjustTwoWatchUniversal(v, mp);
			} else {
				adjustTwoWatchExistential(v, mp);
			}
		}
		
	}
	
	/**
	 * 
	 * @param v :: literal assignment, must be an existential literal
	 * @param watched, positive watched literals
	 * if v is positive, pos is passed in
	 * if v is negative, neg watched is passed in
	 */
	private void adjustTwoWatchExistential(int v, Map<Integer, Integer> watched) {
		if (!f.isMax(v)) MyLog.log(lm, 0, "invalid call to adjustTwoWatchExistential, v is universal");
		Iterator<Map.Entry<Integer, Integer>> iter = watched.entrySet().iterator();
		// entry key = clause id, entry value = watched literal id in the array (existential/universal)
		while (iter.hasNext()) {
			// iterate through the entry set
			Map.Entry<Integer, Integer> entry = iter.next();
			// rule number 0, if the clause is satisfied, skip
			if (this.counter.issat(entry.getKey())) continue;
			// iterate through the universal and see if we can watch one of it to watch
			// such that we watch two universal
			TwoWatchedLiteralFormula.clause_iter++;
			TwoWatchedLiteralClause wr = this.formula.get(entry.getKey());
			boolean found = false;
			for (int i = 0; i < wr.universal.size(); ++i) {
				// has found an unwatched universal literal
				if (!wr.watchedU.contains(i) && !f.assign.hasVar(wr.universal.get(i))) {
					watch(wr.universal.get(i), entry.getKey(), i);
					found = true;
					break;
				}
			}
			
			if (found) {
				wr.watchedE.remove(entry.getValue());
				iter.remove();
				continue;
			}
			
			int uniV = wr.universal.get(wr.watchedU.first());
			for (int i = 0; i < wr.existential.size(); ++i) {
				// has found an unwatched existential literal
				if (!wr.watchedE.contains(i) && !f.assign.hasVar(wr.existential.get(i)) && f.depth(wr.existential.get(i)) < f.depth(uniV)) {
					// watch it
					watch(wr.existential.get(i), entry.getKey(), i);
					found = true;
					break;
				}
			}
			
			if (found) {
				// we can saftely unwatch the current existential literal
				wr.watchedE.remove(entry.getValue());
				iter.remove();
				continue;
			}
			
			// if both steps fail, we know -uniV is unit literal
			if (!found) this.addUnit(-uniV, entry.getKey().intValue());
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
		while (iter.hasNext()) {
			// again simple case, when the clause is satisfied, ignore it
			Map.Entry<Integer, Integer> entry = iter.next();
			if (this.counter.issat(entry.getKey())) continue;
			TwoWatchedLiteralFormula.clause_iter++;
			// the clause that contains this watched universal literal
			TwoWatchedLiteralClause wr = this.formula.get(entry.getKey());
			// if we are watching two universal literals
			if (wr.watchedU.size() == 2) {
				boolean found = false;
				// simpler case, find an universal to replace the watched literal
				for (int i = 0; i < wr.universal.size(); ++i) {
					// has found an unwatched universal literal
					if (!wr.watchedU.contains(i) && !this.f.assign.hasVar(wr.universal.get(i))) {
						watch(wr.universal.get(i), entry.getKey(), i);
						found = true;
						break;
					}
				}

				if (found) {
					wr.watchedU.remove(entry.getValue());
					iter.remove();
					continue;
				}
				
				// complicated case, we must find a universal that is outer of e_other
				// uniV is the u_other described in the paper
				int uniV = wr.universal.get(wr.watchedU.first());
				if (uniV == v) uniV = wr.universal.get(wr.watchedU.last());
				for (int i = 0; i < wr.existential.size(); ++i) {
					// has found an unwatched existential literal, watch it
					if (!this.f.assign.hasVar(wr.existential.get(i)) && f.depth(wr.existential.get(i)) < f.depth(uniV)) {
						watch(wr.existential.get(i), entry.getKey(), i);
						found = true;
						break;
					}
				}
				
				if (found) {
					// we can safely unwatch the current universal literal
					wr.watchedU.remove(entry.getValue());
					iter.remove();
					continue;
				}
				// otherwise, uniV is unit
				if (!found) this.addUnit(-uniV, entry.getKey());
			} else {
				// if we watch 1 existential and 1 universal
				// we do the following, try to find the two literals such that
				// either 2 existential or 1 existential and 1 universal such that depth(e) > depth(u)
				// if we fail to find 1 existential, we find a contradictory clause
				
				int uniV = -1, uniO = -1;
				for (int i = wr.universal.size() - 1; i >= 0; --i) {
					// has found an unwatched universal, unassigned literal
					if (!wr.watchedU.contains(i) && !this.f.assign.hasVar(wr.universal.get(i))) {
						uniV = i;
						break;
					}
				}
				
				// contradictory case, no unassigned existential
				if (uniV == -1) {
					this.contradict.add(entry.getKey());
					break;
				}
				
				if (wr.watchedE.isEmpty()) MyLog.log(lm, 0, "invariant broken in assignU, no existential watched");
				int existV = wr.existential.get(wr.watchedE.first());
				// if existV is already outside universalV, just unwatch e and watch existV
				if (f.depth(wr.universal.get(uniV)) > f.depth(existV)) {
					wr.watchedU.remove(entry.getValue());
					watch(wr.universal.get(uniV), entry.getKey(), uniV);
					iter.remove();
					continue;
				}
				
				// try to find the other watched literal, case we can find an existential
				for (int i = uniV - 1; i >= 0; --i) {
					if (!wr.watchedE.contains(i) && !this.f.assign.hasVar(wr.universal.get(i))) {
						uniO = i;
						break;
					}
				}
				
				// we find two existentials to substitute
				if (uniO != -1) {
					watch(wr.universal.get(uniO), entry.getKey(), uniO);
					watch(wr.universal.get(uniV), entry.getKey(), uniV);
					wr.watchedU.remove(entry.getValue());
					this.unwatch(existV, entry.getKey());
					iter.remove();
					continue;
				}
				
				// if we find 1 existential and 1 universal
				boolean found = false;
				for (int i = wr.existential.size() - 1; i >= 0; --i) {
					if (!this.f.assign.hasVar(wr.existential.get(i)) && f.depth(wr.existential.get(i)) < f.depth(wr.universal.get(uniV))) {
						this.unwatch(existV, entry.getKey());
						watch(wr.existential.get(i), entry.getKey(), i);
						found = true;
						break;
					}
				}
				
				if (found) {
					watch(wr.universal.get(uniV), entry.getKey(), uniV);
					wr.watchedU.remove(entry.getValue());
					iter.remove();
				} else {
					this.addUnit(-wr.universal.get(uniV), entry.getKey());
				}
			}
		}
	}
	
	@Override
	public void unassign(int v) {
		if (v > 0) {
			for (Integer id : this.varNegToid.get(v)) {
				if (this.counter.getDim() == 2) {
					MyLog.log(lm, 2, "Unassign " + v + " clause id " + id + " content: " + this.formula.get(id));
				}
				this.counter.removesat(id);
			}
		} else {
			for (Integer id : this.varPosToid.get(-v)) {
				if (this.counter.getDim() == 2) {
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
		MyLog.log(lm, 2, "find unit: ", v, this.formula.get(fid));
		this.unit.put(v, fid);
	}
	
	@Override
	public int evaluate() {
		if (!this.contradict.isEmpty() || !this.conflictunit.isEmpty()) return 1;
		return -1;
	}
	
	@Override
	public void init() {
		int i, j;
		for (i = 0 ; i < this.formula.size(); ++i) {
			int cnt = 0;
			for (j = 0 ; j < this.formula.get(i).universal.size() && cnt < 2; ++j, ++cnt) {
				int v = this.formula.get(i).universal.get(j);
				if (v > 0) {
					this.watchedFormulaPos.get(v).put(i, j);
				} else {
					this.watchedFormulaNeg.get(-v).put(i, j);
				}
				this.formula.get(i).watchedU.add(j);
			}
			
			for (j = 0 ; j < this.formula.get(i).existential.size() && cnt < 2; ++j, ++cnt) {
				int v = this.formula.get(i).existential.get(j);
				if (v > 0) {
					this.watchedFormulaPos.get(v).put(i, j);
				} else {
					this.watchedFormulaNeg.get(-v).put(i, j);
				}
				this.formula.get(i).watchedE.add(j);
			}
		}
	}
	
	@Override
	public ConflictSolution getConflict() {
		return null;
	}
	
	@Override
	public ConflictSolution getSolution() {
		if (this.evaluate() != 1) MyLog.log(lm, 0, "try to get satisified term when no terms are satisfied");
		if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.QCDCL) {
			ConflictSolution ret = new ConflictSolutionQCDCL(true);
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
		} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PL) {
			ConflictSolution ret = new PNSLearnReason(true);
			((PNSLearnReason) ret).status = PNSLearnReason.Status.pending;
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
				if (!f.isMax(v)) {
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
		
		int i = this.formula.size() - 1, j, cnt = 0;
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
		
				
		if (TwoWatchedLiteralFormula.depend && tol == 1) {
			f.dependgraph.get(l + f.varsize).add(new Pair<>(unass, i));
			f.tempunit.add(new Pair<>(unass, i));
			if (!f.isMax(unass)) {
				MyLog.log(lm, 0, "we have a problem not UIP");
			}
		}
		
		MyLog.log(lm, 2, "learned cube: ", ret);
		
		if (this.formula.get(i).watchedU.isEmpty()) {
			MyLog.log(lm, 0, "fail to watch 2 literals");
		}
		//System.out.println("another literal " + l + " learn clause " + ret);
	}

}
