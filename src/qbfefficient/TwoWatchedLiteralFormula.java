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
	private String lm = new String("2_WL_FORMULA");
	protected AssignmentStack assign;
	protected int varsize;
	protected QuantifierPrefixVSIDS quantifier;
	private List<TwoWatchedLiteralStack> formula;
	private List<Quantifier> qlist;
	private Set<Integer> permanantUnit;
	protected List<List<Pair<Integer, Integer>>> dependgraph;
	protected Set<Pair<Integer, Integer>> tempunit;
	private boolean locked = false;
	public static enum Method {
		BT, BJ, CDCLSBJ, QCDCL, PBJ
	}
	// static command-line-argument region
	public static int maxLevel = 1;
	public static int maxclause = 2500, maxcube = 500;
	public static long setcount = 0, clause_iter = 0, truecount = 0, falsecount = 0;
	public static boolean timer = true, depend = false, debug = false, rand = false, vsids = false;
	public static long prunE = 0, prunU = 0;
	public static Method solvertype = Method.PBJ;
	public TwoWatchedLiteralFormula(int n) {
		this.varsize = n;
		this.tempunit = new TreeSet<>();
		this.assign = new AssignmentStack();
		this.quantifier = new QuantifierPrefixVSIDS(n);
		this.formula = new ArrayList<>();
		this.formula.add(new TwoWatchedLiteralClauseStack(n, this, 0));
		this.formula.add(new TwoWatchedLiteralClauseStack(n, this, 1));
		this.formula.add(new TwoWatchedLiteralCubeStack(n, this, 2));
		this.permanantUnit = new TreeSet<>();
		this.qlist = new ArrayList<>();
		this.dependgraph = new ArrayList<>();
		for (int i = 0 ; i <= 2 * n; ++i) this.dependgraph.add(new ArrayList<>());
	}
	
	@Override
	public int tolLearnClause() {
		return this.formula.get(1).formula.size();
	}
	
	@Override
	public int tolLearnCube() {
		return this.formula.get(2).formula.size();
	}
	
	@Override
	public void addQuantifier(Quantifier q) {
		this.qlist.add(q);
		if (this.qlist.size() == this.quantifier.quantifier.length - 1) this.normalize(0);
	}
	
	@Override
	public void addClause(List<Integer> c) {
		if (locked) MyLog.log(lm, 0, "cannot insert clause after normalized, call learn instead");
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
			System.err.println("try to insert empty clause!\nUNSAT\n");
			System.exit(0);
		}
		
		if (curr.size() == 1) {
			this.permanantUnit.add(curr.get(0).second);
			return;
		}
		
		for (Pair<Integer, Integer> v : curr) list.add(v.second); 
		this.formula.get(0).addClause(list);
	}
	
	@Override
	/**
	 * condition, c must be in minimal form and sorted based on quantifier order
	 */
	public void learn(List<Integer> c, boolean clause) {
		if (c.isEmpty()) return;
		MyLog.log(lm, 2, "learn ", c);
		if (clause) {
			if (c.size() == 1) {
				this.permanantUnit.add(c.get(0));
				return;
			}
			if (TwoWatchedLiteralFormula.maxclause == this.formula.get(1).formula.size()  || c.size() > 50) return;
			this.formula.get(1).learn(c);
		} else {
			if (c.size() == 1) {
				this.permanantUnit.add(c.get(0));
				MyLog.log(lm, 1, "learned unit universal ", c.get(0));
				return;
			}
			if (TwoWatchedLiteralFormula.maxcube == this.formula.get(2).formula.size() || c.size() > 50) return;
			this.formula.get(2).learn(c);
		}
	}
	
	@Override
	public void set(int v) {
		if (this.assign.hasVar(v)) return;
		if (TwoWatchedLiteralFormula.timer) TwoWatchedLiteralFormula.setcount += 1;
		this.assign.assign(v, 0, 'N', -1);
		this.quantifier.remove(v);
		this.formula.get(0).set(v);
		this.formula.get(1).set(v);
		this.formula.get(2).set(v);
	}
	
	@Override
	public int depth(int v) {
		if (v < 0) v = -v;
		return this.quantifier.depth[v];
	}
	
	protected int decisionLevel(int v) {
		return this.assign.literal.getOrDefault(-v, -1);
	}
	
	private void undoBJ(ConflictBJ reason) {
		while (!this.assign.literal.isEmpty() && this.assign.peek().second.type != 'N') {
			Pair<Integer, AssignId> pair = this.assign.unassign();
			if (!reason.isSolution()) {
				if (reason.contains(pair.first)) {
					ConflictSolution other = new ConflictBJ(false);
					if (pair.second.id == -1) {
						reason.drop(null, pair.first);
					} else {
						other.addLiteral(this, this.formula.get(0).formula.get(pair.second.id));
					    reason.resolve(other, pair.first, this);
					}
				}
			}
			this.quantifier.insert(pair.first);
			this.formula.get(0).unassign(pair.first);
		}
		
		if (!this.assign.literal.isEmpty()) {
			Pair<Integer, AssignId> pair = this.assign.unassign();
			this.quantifier.insert(pair.first);
			this.formula.get(0).unassign(pair.first);
		}
	}
	
	private void undoPBJ(ConflictBJ reason) {
		while (!this.assign.literal.isEmpty() && this.assign.peek().second.type != 'N') {
			Pair<Integer, AssignId> pair = this.assign.unassign();
			if (reason != null && !reason.isSolution()) {
				MyLog.log(lm, 2, "Before resolution: ", reason);
				if (reason.contains(pair.first)) {
					ConflictSolution other = new ConflictBJ(false);
					if (pair.second.id == -1) {
						reason.drop(null, pair.first);
					} else {
						other.addLiteral(this, this.formula.get(0).formula.get(pair.second.id));
					    MyLog.log(lm, 2, "resolve with: ", other, " on: ", pair.first);
						reason.resolve(other, pair.first, this);
					}
				}
				MyLog.log(lm, 2, "After resolution: ", reason);
			}
			this.quantifier.insert(pair.first);
			this.formula.get(0).unassign(pair.first);
		}
		
		if (!this.assign.literal.isEmpty()) {
			Pair<Integer, AssignId> pair = this.assign.unassign();
			this.quantifier.insert(pair.first);
			this.formula.get(0).unassign(pair.first);
		}
	}
	
	private void undoCDCLSBJ(ConflictCDCLSBJ reason) {
		while (!this.assign.literal.isEmpty() && this.assign.peek().second.type != 'N') {
			Pair<Integer, AssignId> pair = this.assign.unassign();
			MyLog.log(lm, 2, "propagate reason: ", reason, " split literal: ", pair.first, " reason type: ", reason.isSolution());
			if (!reason.isSolution()) {
				if (reason.contains(-pair.first)) {
					ConflictSolution other = new ConflictCDCLSBJ(false);
					if (pair.second.id == -1) {
						List<Integer> vc = new ArrayList<>();
						vc.add(pair.first);
						other.addAssignment(this, vc);
						reason.resolve(other, pair.first, this);
						
					} else {
						other.addLiteral(this, this.formula.get(pair.second.dimension).formula.get(pair.second.id));
						reason.resolve(other, pair.first, this);
					}
				}
			}
			this.quantifier.insert(pair.first);
			this.formula.get(0).unassign(pair.first);
			this.formula.get(1).unassign(pair.first);
		}
		
		if (!this.assign.literal.isEmpty()) {
			Pair<Integer, AssignId> pair = this.assign.unassign();
			boolean learned = reason.isUIP(this, pair.first);
			List<Integer> ret = null;
			if (learned) {
				ret = reason.allLiteral();
				//for (Integer v : ret) {
				//	this.quantifier.score[Math.abs(v)] += 2.0;
				//}
			}
			this.quantifier.insert(pair.first);
			this.formula.get(0).unassign(pair.first);
			this.formula.get(1).unassign(pair.first);
			if (learned) {
				this.learn(ret, true);
			}
		}
		
		if (reason.size() == 0 && !reason.satisfied) {
			MyLog.log(lm, 1, "empty clause learned");
		} else if (reason.size() == 0 && reason.satisfied) {
			MyLog.log(lm, 1, "empty reason for satisfiability derived");
		}
	}
	
	private void undoQCDCL(ConflictSolutionQCDCL reason) {
		while (!this.assign.literal.isEmpty() && this.assign.peek().second.type != 'N') {
			Pair<Integer, AssignId> pair = this.assign.unassign();
			MyLog.log(lm, 2, "propagate reason: ", reason, " split literal: ", pair.first, " reason type: ", reason.isSolution());
			if (!reason.isSolution()) {
				if (reason.contains(-pair.first) && isMax(pair.first)) {
					ConflictSolution other = new ConflictSolutionQCDCL(false);
					if (pair.second.id == -1) {
						List<Integer> vc = new ArrayList<>();
						vc.add(pair.first);
						other.addAssignment(this, vc);
						reason.resolve(other, pair.first, this);
					} else {
						other.addLiteral(this, this.formula.get(pair.second.dimension).formula.get(pair.second.id));
						reason.resolve(other, pair.first, this);
					}
				}
			} else {
				if (reason.contains(pair.first) && !isMax(pair.first)) {
					ConflictSolution other = new ConflictSolutionQCDCL(true);
					if (pair.second.id == -1) {
						List<Integer> vc = new ArrayList<>();
						vc.add(-pair.first);
						other.addAssignment(this, vc);
						reason.resolve(other, pair.first, this);
						
					} else {
						other.addLiteral(this, this.formula.get(pair.second.dimension).formula.get(pair.second.id));
						reason.resolve(other, pair.first, this);
					}
				}
			}
			this.quantifier.insert(pair.first);
			this.formula.get(0).unassign(pair.first);
			this.formula.get(1).unassign(pair.first);
			this.formula.get(2).unassign(pair.first);
		}
		
		if (!this.assign.literal.isEmpty()) {
			Pair<Integer, AssignId> pair = this.assign.unassign();
			MyLog.log(lm, 2, "branching variable: ", pair.first);
			boolean learned = reason.isUIP(this, pair.first)  && (reason.satisfied != isMax(pair.first));
			List<Integer> ret = null;
			if (learned) {
				ret = reason.allLiteral();
			}
			this.quantifier.insert(pair.first);
			this.formula.get(0).unassign(pair.first);
			this.formula.get(1).unassign(pair.first);
			this.formula.get(2).unassign(pair.first);
			if (learned && !reason.satisfied) {
				this.learn(ret, true);
			} else if (learned && reason.isSolution()) {
				this.learn(ret, false);
			}
		}
		
		if (reason.size() == 0 && !reason.satisfied) {
			MyLog.log(lm, 1, "empty clause learned");
		} else if (reason.size() == 0 && reason.satisfied) {
			MyLog.log(lm, 1, "empty term learned");
		}
	}
	
	@Override
	public void undo(ConflictSolution reason) {
	    if (TwoWatchedLiteralFormula.solvertype == Method.BT) {
	    	while (!this.assign.literal.isEmpty() && this.assign.peek().second.type != 'N') {
				Pair<Integer, AssignId> pair = this.assign.unassign();
				this.quantifier.insert(pair.first);
				this.formula.get(0).unassign(pair.first);
			}
			
			if (!this.assign.literal.isEmpty()) {
				Pair<Integer, AssignId> pair = this.assign.unassign();
				this.quantifier.insert(pair.first);
				this.formula.get(0).unassign(pair.first);
			}
	    } else if (TwoWatchedLiteralFormula.solvertype == Method.BJ) {
	    	if (reason == null) MyLog.log(lm, 0, "null reason for backjumping solver");
			undoBJ((ConflictBJ) reason);
		} else if (TwoWatchedLiteralFormula.solvertype == Method.CDCLSBJ) {
			if (reason == null) MyLog.log(lm, 0, "null reason for cdclsbj solver");
			undoCDCLSBJ((ConflictCDCLSBJ) reason);
		} else if (TwoWatchedLiteralFormula.solvertype == Method.QCDCL) {
			if (reason == null) MyLog.log(lm, 0, "null reason for qcdcl solver");
			undoQCDCL((ConflictSolutionQCDCL) reason);
		} else if (TwoWatchedLiteralFormula.solvertype == Method.PBJ) {
			undoPBJ((ConflictBJ) reason);
		}
	}
	
	@Override
	public int evaluate() {
		int v1 = this.formula.get(0).evaluate();
		int v2 = this.formula.get(1).evaluate();
		if (v1 == 0 || v2 == 0) {
			return 0;
		}
		
		if (v1 == 1 || this.formula.get(2).evaluate() == 1) {
			return 1;
		}
		return -1;
	}
	
	@Override
	public void simplify() {
		// System.out.println("enter simp");
		for (Integer v : this.permanantUnit) {
			if (evaluate() != -1) break;
			if (this.assign.hasLiteral(v)) continue;
			if (isMax(v)) {
				propagate(v, 0, 'U', -1);
			} else {
				propagate(v, 2, 'U', -1);
			}
		}
		
		
		if (TwoWatchedLiteralFormula.depend) {
			for (Pair<Integer, Integer> v : this.tempunit) {
				if (evaluate() != -1) break;
				if (this.assign.hasLiteral(v.first)) continue;
				propagate(v.first, 0, 'U', v.second);
			}
		}
		
		while ((!this.formula.get(0).unit.isEmpty() || (!this.formula.get(1).unit.isEmpty()) || (!this.formula.get(2).unit.isEmpty())) && evaluate() == -1) {
			Map.Entry<Integer, Integer> entry = null;
			while (evaluate() == -1 && !this.formula.get(0).unit.isEmpty()) {
				entry = this.formula.get(0).unit.firstEntry();
				propagate(entry.getKey(), 0, 'U', entry.getValue());
				this.formula.get(0).unit.remove(entry.getKey());
			}
			
			while (evaluate() == -1 && !this.formula.get(1).unit.isEmpty()) {
				entry = this.formula.get(1).unit.firstEntry();
				propagate(entry.getKey(), 1, 'U', entry.getValue());
				this.formula.get(1).unit.remove(entry.getKey());
			}
			
			while (evaluate() == -1 && !this.formula.get(2).unit.isEmpty()) {
				entry = this.formula.get(2).unit.firstEntry();
				propagate(entry.getKey(), 2, 'U', entry.getValue());
				this.formula.get(2).unit.remove(entry.getKey());
			}
		}
		
		this.formula.get(0).unit.clear();
		this.formula.get(1).unit.clear();
		this.formula.get(2).unit.clear();
	}
	
	private void propagate(int v, int d, char type, int id) {
		if (this.assign.hasLiteral(v)) {
			return;
		}
		
		if (this.assign.hasLiteral(-v)) {
			if (id != -1) {
				this.formula.get(d).contradict.add(id);
			} else {
				if (isMax(v)) {
					this.formula.get(0).conflictunit.add(v);
				} else {
					this.formula.get(2).conflictunit.add(v);
				}
			}
			return;
		}
		if (TwoWatchedLiteralFormula.timer) TwoWatchedLiteralFormula.setcount += 1;
		this.assign.assign(v, d, type, id);
		this.quantifier.remove(v);
		this.formula.get(0).set(v);
		this.formula.get(1).set(v);
		this.formula.get(2).set(v);
		if (evaluate() == -1 && isMax(v) && this.permanantUnit.contains(-v)) {
			this.formula.get(0).conflictunit.add(-v);
		}
		
		if (evaluate() == -1 && !isMax(v) && this.permanantUnit.contains(v)) {
			this.formula.get(2).conflictunit.add(v);
		}
	}
	
	@Override
	public Quantifier peek() {
		if (!locked) MyLog.log(lm, 0, "formula not normalized");
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
			for (int i = 0 ; i < this.formula.get(0).formula.size(); ++i) {
				for (Integer v : this.formula.get(0).formula.get(i).existential) {
					this.quantifier.score[Math.abs(v)] += 1.0;
				}
                
				for (Integer v : this.formula.get(0).formula.get(i).universal) {
					this.quantifier.score[Math.abs(v)] += 1.0;
				}
			}
			this.quantifier.normalized();
			this.formula.get(0).init();
			this.formula.get(1).init();
			this.formula.get(2).init();
			this.locked = true;
		} else {
			// TODO, things to do during restart
		}
	} 
	
	@Override
	public ConflictSolution getReason() {
		ConflictSolution ret = null;
		if (evaluate() == 1) {
			MyLog.log(lm, 3, "reach a solution node");
			if (this.formula.get(2).evaluate() == -1) {
				return this.formula.get(0).getSolution();
			}
			
			return this.formula.get(2).getSolution();
		} else if (evaluate() == 0) {
			if (this.formula.get(0).evaluate() == 0) {
				ret = this.formula.get(0).getConflict();
			}
			
			if (this.formula.get(1).evaluate() == 0) {
				if (ret == null) {
					ret = this.formula.get(1).getConflict();
				} else {
					this.formula.get(1).getConflict();
				}
			}
		}
		
		if (ret == null) MyLog.log(lm, 0, "Wrong time to call getReason, no conflict found evaluate= ", evaluate());
		
		MyLog.log(lm, 3, "meet conflict ", ret);
		return ret;
	}

	@Override
	public boolean isassigned(int v) {
		return this.assign.hasVar(v);
	}

	@Override
	public TwoWatchedLiteralClause unitId(int v) {
		// TODO Auto-generated method stub
		AssignId cid = this.assign.getUnit(v);
		if (cid == null) return null;
		if (cid.type == 'U' && cid.id != -1) {
			MyLog.log(lm, 2, "long distance resolution with ", this.formula.get(cid.dimension).formula.get(cid.id) , " unit: ", v, " id= ", cid.id);
			return this.formula.get(cid.dimension).formula.get(cid.id);
		}
		if (cid.type == 'U' && cid.id == -1) {
			TwoWatchedLiteralClause c = new TwoWatchedLiteralClause();
			if (isMax(v)) {
				c.existential.add(v);
			} else {
				c.universal.add(v);
			}
			return c;
		} 
		return null;
	}
}
