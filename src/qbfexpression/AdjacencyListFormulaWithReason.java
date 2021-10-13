package qbfexpression;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

import qbfefficient.TwoWatchedLiteralFormula;
import qbfsolver.ResultGenerator;
// import utilstructure.BOMHCount;
import utilstructure.BOMHVector;
// import utilstructure.BHOMvector;
import utilstructure.Pair;

public class AdjacencyListFormulaWithReason implements CnfExpression {
    public QuantifierBlock block;
	public int n, fcount;
	public List<AdjacencyListClauseWithReason> formula;
	public List<Set<Integer>> varToformulainit;
	public List<Set<Integer>> varToformula;
	public List<LinkedList<Integer>> usedformula;
	// universal count, proved count, disproved count
	public int proved = 0, disproved = 0;
	// record the assigned variables in the last assignment
	public LinkedList<LinkedList<Integer>> assigned;
	protected HashSet<Integer> pure;
	protected HashSet<Integer> unit;
	protected HashSet<Integer> useless;
	private Set<Integer> provedformula;
	protected Set<Integer> disprovedformula;
	private LinkedList<Integer> usedvar;
	private boolean normalized;
	public LinkedList<Pair<Integer, Character>> currentassign;
	private ISolver satsolver;
	public Set<Integer> learnedunit;
	public AdjacencyListFormulaWithReason(int n, int fcount) {
		int i;
		this.block = new FrequencyBlock(n);
		this.n = n;
		this.normalized = false;
		this.fcount = fcount;
		this.formula = new ArrayList<>();
		this.assigned = new LinkedList<>();
		this.provedformula = new TreeSet<>();
		this.disprovedformula = new TreeSet<>();
		this.usedvar = new LinkedList<>();
		this.varToformula = new ArrayList<>();
		this.varToformulainit = new ArrayList<>();
		this.usedformula = new ArrayList<>();
		for (i = 0 ; i <= n; ++i) {
			this.block.isexist[i] = true;
			this.block.poscount[i] = this.block.negcount[i] = this.block.order[i] = 0;
			this.varToformula.add(new HashSet<>());
			this.varToformulainit.add(new HashSet<>());
			this.usedformula.add(new LinkedList<>());
		}
		this.pure = new HashSet<>();
		this.unit = new HashSet<>();
		this.useless = new HashSet<>();
		this.currentassign = new LinkedList<>();
		this.satsolver = SolverFactory.newDefault();
		this.satsolver.newVar(this.n + 1);
		this.satsolver.setExpectedNumberOfClauses(this.fcount);
		this.satsolver.setTimeout(30000);
	}
	
	public void incProved(int inc) {
		this.proved += inc;
	}
	
	public void incDisproved(int inc) {
		this.disproved += inc;
	}
	
	private void setNormal() {
		this.normalized = true;
	}
	
	public int getLevel(int val) {
		if (val < 0) val = -val;
		return this.block.order[val];
	}
	
	public boolean isMax(int val) {
		if (val < 0) val = -val;
		return this.block.isexist[val];
	}
	
    public void updateCounter(int v, int inc) {
		if (v > 0) {
			this.block.updatePositive(v, inc);
			if (this.block.negcount[v] > 0 && this.block.poscount[v] == 0) {
				pure.add(-v);
			}
			
			if (this.block.negcount[v] == 0 && this.block.poscount[v] > 0) {
				pure.add(v);
			}
			
			if (this.block.poscount[v] + this.block.negcount[v] == 0) {
				useless.add(v);
				pure.remove(v);
				pure.remove(-v);
				unit.remove(v);
				unit.remove(-v);
			}
			
			if (this.block.negcount[v] > 0 || this.block.poscount[v] > 0) {
				useless.remove(v);
			}
		} else {
			v = -v;
			this.block.updateNegative(v, inc);
			if (this.block.negcount[v] > 0 && this.block.poscount[v] == 0) {
				pure.add(-v);
			}
			
			if (this.block.negcount[v] == 0 && this.block.poscount[v] > 0) {
				pure.add(v);
			}
			
			if (this.block.poscount[v] + this.block.negcount[v] == 0) {
				useless.add(v);
				pure.remove(-v);
				pure.remove(v);
				unit.remove(v);
				unit.remove(-v);
			}
			
			if (this.block.negcount[v] > 0 || this.block.poscount[v] > 0) {
				useless.remove(v);
			}
		}
		
		if (this.block.poscount[v] > 0 && this.block.negcount[v] > 0) {
			pure.remove(v);
			pure.remove(-v);
		}
		 
	}
	
    public void addUnit(int v) {
		this.unit.add(v);
	}
    
    public int getFreq(int id) {
		if (id < 0) id = -id;
		return getNegfreq(id) + getPosfreq(id);
	}

	public int getNegfreq(int id) {
		if (id < 0) id = -id;
		return this.block.negcount[id];
	}

	public int getPosfreq(int id) {
		if (id < 0) id = -id;
		return this.block.poscount[id];
	}
    
	public void addDisprove(int id, boolean direction) {
		if (direction) {
			this.disprovedformula.add(id);
		} else {
			this.disprovedformula.remove(id);
		}
	}
	
    public void addProved(int id, boolean direction) {
		if (direction) {
			this.provedformula.add(id);
			List<Integer> list = this.formula.get(id).getAll();
			for (Integer v : list) {
				this.varToformula.get(Math.abs(v)).remove(id);
			}
		} else {
			this.provedformula.remove(id);
			List<Integer> list = this.formula.get(id).getAll();
			for (Integer v : list) {
				this.varToformula.get(Math.abs(v)).add(id);
			}
		}
	}
    
    private void unassign(int v, Reason r) {
		if (v < 0) v = -v;
		while (!this.usedformula.get(v).isEmpty()) {
			int id = this.usedformula.get(v).pollLast();
			AdjacencyListClauseWithReason d = this.formula.get(id);
			d.set(v, this, -1, id);
			TwoWatchedLiteralFormula.clause_iter++;
		}
		
		boolean debug = ResultGenerator.getCommandLine().getDebug();
		if (debug) {
			System.out.println("unassign " + v);
			System.out.println(this);
			System.out.println(this.currentassign);
		}
		
		if (this.currentassign.isEmpty() || Math.abs(this.currentassign.getLast().first) != v) {
			System.err.println("there's a problem");
			System.err.println(currentassign);
			System.err.println(v);
			System.exit(0);
		} else {
			Pair<Integer, Character> lastassign = this.currentassign.removeLast();
			if (r != null) {
				if (r.satisfied) {
					// for a satisfied reason, we can drop anything other than a branching
					// variable
					if (lastassign.second != 'N' || isMax(lastassign.first)) { 
						r.literals.remove(lastassign.first);
					}
				} else {
					// for existential literal, things are a bit complicated
					if (lastassign.second == 'P' || lastassign.second == 'B' || !isMax(lastassign.first)) {
						r.literals.remove(lastassign.first);
					} else if (lastassign.second == 'U') {
						if (r.contains(lastassign.first)) {
							boolean found = false;
							for (Integer id : this.varToformula.get(Math.abs(v))) {
								AdjacencyListClauseWithReason d = this.formula.get(id);
								if (d.hasUnit(this, lastassign.first)) {
									List<Integer> contradict = d.getContradiction();
									for (Integer cc : contradict) {
										if (isMax(cc)) {
											r.literals.add(-cc);
										}
									}
									
									if (debug) {
										System.out.println("found the unit thing");
										System.out.println(d);
										System.out.println("after unit " + r.literals);
									}
									found = true;
									break;
								}
							}
							
							if (!found) {
								System.err.println("not found!");
								System.exit(0);
							}
						} 
						r.literals.remove(lastassign.first);
						r.literals.remove(-lastassign.first);
					}
				}
			}
		}
	}
    
    private boolean unit_propagation() {
		if (terminal()) return false; 
		if (unit.isEmpty()) return false;
		int v = unit.iterator().next();
		unit.remove(v);
		if (ResultGenerator.learnpreprocess && ResultGenerator.cdcl) {
			System.out.println("learn unit " + v);
			this.learnedunit.add(v);
		}
		if (isMax(v)) {
			this.set(v, 'U');
		} else {
			// System.err.println("universal?");
			this.set(-v, 'U');
		}
		return true;
	}
	
	private boolean pure_literal_elimination() {
		if (terminal()) return false;
		if (pure.isEmpty()) return false;
		if (ResultGenerator.nopure && !ResultGenerator.learnpreprocess) return false;
		int v = pure.iterator().next();
		pure.remove(v);
		if (ResultGenerator.learnpreprocess) {
			System.out.println("learn pure " + v);
			this.learnedunit.add(v);
		}
		if (isMax(v)) {
			this.set(v, 'P');
		} else {
			this.set(-v, 'P');
		}
		return true;
	}
	
	private void eliminate_useless_quantifier() {
		for (Integer id : this.useless) {
			// System.out.println("drop " + id);
			this.dropquantifier(id);
			if (ResultGenerator.learnpreprocess) {
				System.out.println("learn broken " + id);
				this.learnedunit.add(id);
			}
			if (!this.currentassign.isEmpty() && Math.abs(this.currentassign.getLast().first) == Math.abs(id)) {
				this.currentassign.getLast().second = 'B';
			}
		}
	}
	
	private boolean set(int v, char type) {
		if (this.set(v)) {
			this.currentassign.getLast().second = type;
		}
		return false;
	}
    
	@Override
	public int getn() {
		return this.n;
	}
	
	@Override
	public void addquantifier(Quantifier q) {
		this.block.insert(q, this.normalized);
	}

	@Override
	public boolean hasQuantifier() {
		return this.block.quantifiercount > 0;
	}
	
	@Override
	public void addcnf(Disjunction c) {
		List<Integer> ret = c.getLiteral();
		for (int i = 0 ; i < ret.size(); ++i) {
			if (c.evaluate() == 1) {
				this.proved++;
				break;
			}
			int v = ret.get(i);
			this.updateCounter(v, 1);
			if (ret.size() == 1) this.addUnit(v);
			if (v < 0) v = -v;
			varToformula.get(v).add(formula.size());
			varToformulainit.get(v).add(formula.size());
			if (isMax(v)) {
				((AdjacencyListClauseWithReason) c).incExist(1);
			}
		}
		
		formula.add((AdjacencyListClauseWithReason) c);
		// add an empty clause
		if (c.isEmpty() || c.evaluate() == 0) {
			this.disproved++;
			System.err.println("try to insert an empty clause");
			System.out.println("UNSAT");
			System.exit(0);
		}
	}

	@Override
	public Quantifier peek() {
		if (normalized == false) {
			System.err.println("hasn't called normal!");
			System.exit(0);
		}

		if (ResultGenerator.bomh) {
			List<Quantifier> list = this.block.peek(20, this.block.peek().isMax());
			ArrayList<BOMHVector> vc = new ArrayList<>();
			for (Quantifier q : list) {
				BOMHVector curr = new BOMHVector(q);
				for (Integer d : this.varToformula.get(q.getVal())) {
					AdjacencyListClauseWithReason c = this.formula.get(d);
					if (c.evaluate() != -1) continue;
					if (c.contains(q.getVal())) {
						curr.add(c.getExist(), true);
					} else {
						curr.add(c.getExist(), false);
					}
					
				}
				curr.normalize();
				vc.add(curr);
			}
			
			Collections.sort(vc);
			// System.out.println(vc);
			return vc.get(0).getQuantifier();
		}
		return this.block.peek();
	}

	@Override
	public int maxSameQuantifier(boolean type) {
		if (normalized == false) {
			System.err.println("hasn't called normal!");
			System.exit(0);
		}
		return this.block.maxSameQuantifier(type);
	}

	@Override
	public List<Quantifier> peek(int count, boolean type) {
		if (normalized == false) {
			System.err.println("hasn't called normal!");
			System.exit(0);
		}
		return this.block.peek(count, type);
	}

	@Override
	public void dropquantifier() {
		int v = this.peek().getVal();
		this.block.dropQuantifier(v);
	}

	@Override
	public void dropquantifier(int v) {
		if (this.block.hasQuantifier(v)) {
			this.usedvar.add(v);
			this.currentassign.add(new Pair<Integer, Character>(v, 'N'));
		}
		this.block.dropQuantifier(v);
	}
    
	private boolean terminal() {
		if (this.disproved > 0) return true;
		if (this.proved == this.fcount) return true;
		return false;
	}
	
	@Override
	public boolean set(int v) {
		if (this.terminal()) return false;
		if (!this.block.hasQuantifier(v)) return false;
		List<Integer> list = new ArrayList<Integer>(this.varToformula.get(Math.abs(v)));
		for (Integer id : list) {
			if (this.provedformula.contains(id)) continue;
			AdjacencyListClauseWithReason d = this.formula.get(id);
			d.set(Math.abs(v), this, v > 0 ? 1 : 0, id);
			TwoWatchedLiteralFormula.clause_iter++;
			this.usedformula.get(Math.abs(v)).add(id);
		}
		if (TwoWatchedLiteralFormula.timer) TwoWatchedLiteralFormula.setcount += 1;
		this.dropquantifier(v);
		return true;
	}

	@Override
	public void setSatisfied(boolean val) {
		if (val) {
			this.proved = this.fcount;
			this.disproved = 0;
		} else {
			this.disproved = 1;
		}
	}

	@Override
	public void simplify() {
		boolean t1 = true;
		boolean t2 = true;
		while (t1 || t2) {
			t1 = unit_propagation();
			t2 = pure_literal_elimination();
		}
		
		this.eliminate_useless_quantifier();
		this.unit.clear();
		this.pure.clear();
		this.useless.clear();
	}
	
	public void undo(Reason r) {
		if (!this.assigned.isEmpty()) {
			LinkedList<Integer> last = assigned.pollLast();
			while (!last.isEmpty()) {
				int it = last.pollLast();
				it = Math.abs(it);
				this.addquantifier(this.block.quantifiers[it]);
				this.unassign(it, r);
			}
		}
		
		this.pure.clear();
		this.unit.clear();
		this.useless.clear();
	}
	
	@Override
	public void undo() {
		if (!this.assigned.isEmpty()) {
			LinkedList<Integer> last = assigned.pollLast();
			while (!last.isEmpty()) {
				int it = last.pollLast();
				it = Math.abs(it);
				this.addquantifier(this.block.quantifiers[it]);
				this.unassign(it, null);
			}
		}
		this.pure.clear();
		this.unit.clear();
		this.useless.clear();
	}

	@Override
	public void commit() {
		if (!this.usedvar.isEmpty()) {
			LinkedList<Integer> st = new LinkedList<>(usedvar);
			usedvar.clear();
			this.assigned.add(st);
		}
	}

	@Override
	public void normalize() {
		this.fcount = this.formula.size();
		for (int i = 1; i <= n; ++i) {
			if (block.hasQuantifier(i)) continue;
			// this.addquantifier();
			this.block.prepend(new Quantifier(isMax(i), i));
			// System.out.println("not normal");
		}
		
		for (int i = 1; i <= n; ++i) {
			if (this.getFreq(i) == 0) {
				useless.add(i);
			}
		}
		
		this.setNormal();
		eliminate_useless_quantifier();
		// System.out.println(this.block.size());
		
		this.block.unicount = 0;
		for (int i = 1; i <= n; ++i) {
			if (this.getFreq(i) > 0 && !this.isMax(i)) this.block.unicount++;
			if (this.getPosfreq(i) == 0 && this.getNegfreq(i) != 0) this.pure.add(-i);
			if (this.getPosfreq(i) > 0 && this.getNegfreq(i) == 0) this.pure.add(i);
		}
		for (int i = 0; i < formula.size(); ++i) {
			int lv = Integer.MAX_VALUE, cnt = 0, target = 0;
			List<Integer> ret = this.formula.get(i).getLiteral();
			for (Integer v : ret) {
				if (this.isMax(v)) {
					target = v;
					cnt++;
				} else {
					lv = Math.min(lv, this.getLevel(target));
				}
			}
			
			if (target != 0 && cnt == 1 && lv > this.getLevel(target)) {
				this.addUnit(target);
				//System.out.println(this.formula.get(i) + " has unit " + target);
			}
		}
		
		//System.out.println(unit);
		this.simplify();
		this.commit();
		for (AdjacencyListClauseWithReason d : this.formula) {
			if (d.evaluate() == -1) {
				List<Integer> li = d.getLiteral();
				List<Integer> list = new ArrayList<>();
				for (Integer it : li) {
					list.add(it);
				}
				int [] clause = list.stream().mapToInt(Integer::intValue).toArray();
				try {
					this.satsolver.addClause(new VecInt(clause));
				} catch (ContradictionException e) {
					System.out.println("UNSAT");
					System.exit(0);
				}
			}
		}
		
		//System.out.println(this.block.size());
		//System.out.println(this.currentassign);
		//this.currentassign.clear();
		//System.exit(0);
	}
	
	private boolean checktrue(int v, HashSet<Integer> ass) {
		boolean debug = ResultGenerator.getCommandLine().getDebug();
		if (debug) {
			System.out.println("----check------- " + v + " --------");
			System.out.println("current assign " + ass);
		}
		for (Integer id : this.varToformulainit.get(Math.abs(v))) {
			if (debug) System.out.println("formula with id= " + id);
			AdjacencyListClauseWithReason d = this.formula.get(id);
			boolean in = false, ok = false;
			List<Integer> lit = d.getAll();
			for (Integer l : lit) {
				if (l == v) {
					in = true;
				}
				
				if (l != v && ass.contains(l)) {
					if (debug) System.out.println("contains assign " + l + " " + d);
					ok = true;
				}
			}
			
			if (in && !ok) return false;
		}
		//System.out.println("check ok" + v);
		return true;
	}
	
	private void checkvalid(Set<Integer> ass) {
		int i;
		
		for (i = 0 ; i < formula.size(); ++i) {
			AdjacencyListClauseWithReason d = formula.get(i);
			boolean ok = false;
			for (Integer v : d.getAll()) {
				if (ass.contains(v)) {
					ok = true;
					break;
				}
			}
			
			if (!ok) {
				System.err.println("wrong on " + d);
				System.err.println("ass= " + ass);
				System.exit(0);
			}
		}
	}
	
	public Reason getReason() {
		int res = -1;
		boolean debug = ResultGenerator.getCommandLine().getDebug();
		int[] curr = null;
		if (debug) {
			System.out.println("before we compute the reason");
			System.out.println(this.currentassign);
			System.out.println(this);
		}
		
		IVecInt vc = new VecInt(), vcu = new VecInt();
		if (this.disproved > 0) {
			res = 0;
		} else if (this.proved == this.fcount) {
			res = 1;
		} else {
			if (this.block.unicount == 0) {
				for (Pair<Integer, Character> p : this.currentassign) {
					vc.push(p.first);
					if (!isMax(p.first)) {
						vcu.push(p.first);
					}
				}
				
				
				try {
					curr = this.satsolver.findModel(vc);
					if (curr != null) {
						res = 2;
					} else {
						res = -2;
					}
				} catch (TimeoutException e) {
					e.printStackTrace();
					System.exit(0);
				}
			}
		}
		
		if (res == -1) {
			System.err.println("invalid call to reason!");
			System.exit(1);
		}
		
		Reason ret = new Reason();
		ret.satisfied = (res == 1 || res == 2);
		// SAT solver is called
		if (res == -2) {
			boolean fg = true;
			// System.out.println("UNSAT reason with SAT");
			for (Pair<Integer, Character> p : this.currentassign) {
				try {
					if (fg && !this.satsolver.isSatisfiable(vcu)) {
						/*System.out.println(this.satsolver.isSatisfiable());
						System.out.println(this.currentassign);
						System.out.println(vcu + " " + ret.literals);*/
						break;
					}
					fg = false;
				} catch (TimeoutException e) {
					e.printStackTrace();
					System.exit(0);
				}
				
				if (isMax(p.first) && p.second == 'N') {
					vcu.push(p.first);
					ret.literals.add(p.first);
					fg = true;
				}
			}
			
			//System.out.println(vcu + " " + ret.literals);
		} else {
			if (res == 1 || res == 2) {
				HashSet<Integer> ass = new HashSet<>();
				LinkedList<Integer> li = new LinkedList<>();
				if (res == 2) {
					for (int i = 0 ; i < curr.length; ++i) {
						ass.add(curr[i]);
						//System.out.print(curr[i] + " ");
					}
					//System.out.println();
				}
				for (Pair<Integer, Character> p : this.currentassign) {
					if (p.second != 'B') {
						ass.add(p.first);
					}
					if (!isMax(p.first) && p.second != 'B') {
						li.add(p.first);
					}	
				}
				
				Iterator<Integer> iter = li.descendingIterator();
				
				while (iter.hasNext()) {
					int cand = iter.next();
					if (checktrue(cand, ass)) {
						iter.remove();
						ass.remove(cand);
					}
				}
				ret.literals.addAll(li);
				if (debug) checkvalid(ass);
			} else {
				if (!this.disprovedformula.isEmpty()) {
					Iterator<Integer> biter = this.disprovedformula.iterator();
					int id = biter.next();
					for (Integer cc : this.formula.get(id).getContradiction()) {
						if (isMax(cc)) {
							ret.literals.add(-cc);
						}
					}
				} else {
					System.err.println("strange behavior");
					System.exit(1);
				}
			}
		}
		
		if (debug) {
			System.out.println("after we compute the reason");
			System.out.println(res + " " + ret.literals);
			System.out.println(this.currentassign);
			System.out.println(this);
		}
		
		return ret;
	}

	@Override
	public int evaluate() {
		if (this.disproved > 0) return 0;
		if (this.proved == this.fcount) return 1;
		if (ResultGenerator.satsolver) {
			if (this.block.unicount == 0) {
				IVecInt vc = new VecInt();
				for (Pair<Integer, Character> p : this.currentassign) {
					vc.push(p.first);
				}
				
				//System.out.println(vc);
				try {
					boolean curr = this.satsolver.isSatisfiable(vc);
					if (curr) {
						return 1;
					}
					
					return 0;
				} catch (TimeoutException e) {
					e.printStackTrace();
				}
				return -1;
			}
		}
		return -1;
	}

	@Override
	public CnfExpression duplicate() {
		return this;
	}
	
	private boolean checkTrivialtruth() {
		ISolver s = SolverFactory.newDefault();
		s.setTimeout(900);
		s.newVar(this.n + 1);
		s.setExpectedNumberOfClauses(this.fcount);
		for (AdjacencyListClauseWithReason d : this.formula) {
			if (d.evaluate() == -1) {
				List<Integer> li = d.getLiteral();
				List<Integer> list = new ArrayList<>();
				for (Integer it : li) {
					if (isMax(it)) {
						list.add(it);
					}
				}
				int [] clause = list.stream().mapToInt(Integer::intValue).toArray();
				try {
					s.addClause(new VecInt(clause));
				} catch (ContradictionException e) {
					return false;
				}
			}
		}
		
		boolean ret = false;
		try {
			ret = s.isSatisfiable();
		} catch (TimeoutException e) {
			e.printStackTrace();
		}
		
		return ret;
	}
	
	private boolean checkTrivialfalse() {
		ISolver s = SolverFactory.newDefault();
		s.setTimeout(900);
		s.newVar(this.n + 1);
		s.setExpectedNumberOfClauses(this.fcount);
		for (AdjacencyListClauseWithReason d : this.formula) {
			if (d.evaluate() == -1) {
				List<Integer> list = d.getLiteral();
				int [] clause = list.stream().mapToInt(Integer::intValue).toArray();
				try {
					s.addClause(new VecInt(clause));
				} catch (ContradictionException e) {
					return true;
				}
			}
		}
		
		boolean ret = false;
		try {
			ret = s.isSatisfiable();
		} catch (TimeoutException e) {
			e.printStackTrace();
		}
		
		return ret ? false : true;
	}
	
	
	private int evaluate_1() {
		if (this.disproved > 0) return 0;
		if (this.proved == this.fcount) return 1;
		if (ResultGenerator.satsolver) {
			if (this.block.unicount == 0) {
				ISolver s = SolverFactory.newDefault();
				s.setTimeout(900);
				s.newVar(this.n + 1);
				s.setExpectedNumberOfClauses(this.fcount);
				for (Disjunction d : this.formula) {
					if (d.evaluate() != -1) continue;
					List<Integer> list = d.getLiteral();
					int [] clause = list.stream().mapToInt(Integer::intValue).toArray();
					try {
						s.addClause(new VecInt(clause));
					} catch (ContradictionException e) {
						return 0;
					}
				}
				
				try {
					boolean curr = s.isSatisfiable();
					if (curr) {
						return 1;
					}
					
					return 0;
				} catch (TimeoutException e) {
					e.printStackTrace();
				}
				return -1;
			}
		}
		return -1;
	}
	
	public String toString() {
		StringBuilder ret = new StringBuilder();
		int val = evaluate_1();
		if (val == 1 || (val == -1 && checkTrivialtruth())) {
			ret.append("p cnf 1 0\n");
			return ret.toString();
		} else if (val == 0 || checkTrivialfalse()) {
			ret.append("p cnf 1 1\n0\n");
			return ret.toString();
		}
		
		TreeMap<Integer, Integer> squeeze = new TreeMap<>();
		String rett2 = block.toString(squeeze);
		Set<String> oc = new HashSet<>();
		int acccnt = 0;
		/*if (ResultGenerator.cdcl) {
			this.formula.sort(new FormulaComparator());
		}*/
		for (AdjacencyListClauseWithReason d : this.formula) {
			if (d.evaluate() == -1) {
				List<Integer> list = d.getLiteral();
				if (d.isLearned() && list.size() > 16) continue;
				StringBuilder cu = new StringBuilder();
				ArrayList<Integer> now = new ArrayList<>();
				for (Integer it : list) {
					if (it < 0) {
						if (!squeeze.containsKey(-it)) {
							//System.out.println("here we are");
							continue;
						}
						now.add(-squeeze.get(-it));
					} else {
						if (!squeeze.containsKey(it)) {
							//System.out.println("bad here we are");
							continue;
						}
						now.add(squeeze.get(it));
					}
				}
				
				Collections.sort(now);
				for (Integer it : now) {
					cu.append(it);
					cu.append(' ');
				}
				
				cu.append("0\n");
				if (!oc.contains(cu.toString())) {
					ret.append(cu);
					oc.add(cu.toString());
					acccnt++;
				}
			}
		}
		
		
		return "p cnf " + this.block.size() + " " + acccnt + "\n" + rett2 + ret.toString();
	}

	public Reason checkTrivial() {
		IVecInt vc = new VecInt(), vcu = new VecInt();
		for (Pair<Integer, Character> p : this.currentassign) {
			vc.push(p.first);
			if (!isMax(p.first)) {
				vcu.push(p.first);
			}
		}
		
		List<Integer> uni = this.block.getUniverse();
		for (Integer v : uni) {
			Random r = new Random();
			if (r.nextInt(2) == 1) {
				vc.push(v);
				vcu.push(v);
			} else {
				vc.push(-v);
				vcu.push(-v);
			}
		}
		
		try {
			if (this.satsolver.isSatisfiable(vc)) return null;
		} catch (TimeoutException e) {
			e.printStackTrace();
		}
		
		boolean fg = true;
		Reason ret = new Reason();
		for (Pair<Integer, Character> p : this.currentassign) {
			try {
				if (fg && !this.satsolver.isSatisfiable(vcu)) {
					break;
				}
				fg = false;
			} catch (TimeoutException e) {
				e.printStackTrace();
				System.exit(0);
			}
			
			if (isMax(p.first) && p.second == 'N') {
				vcu.push(p.first);
				ret.literals.add(p.first);
				fg = true;
			}
		}
		
		// System.out.println("other uni= " + uni);
		System.out.println("trivial condition triggered!");
		//System.out.println(ret.literals);
		return ret;
	}
}
