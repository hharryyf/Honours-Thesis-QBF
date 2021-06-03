package qbfexpression;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import utilstructure.Pair;

public class AdjacencyListFormula implements CnfExpression {
    public QuantifierBlock block;
	public int n, fcount;
	public List<AdjacencyListClause> formula;
	public List<Set<Integer>> varToformulainit;
	public List<Set<Integer>> varToformula;
	public List<LinkedList<Integer>> usedformula;
	// universal count, proved count, disproved count
	public int proved = 0, disproved = 0;
	// record the assigned variables in the last assignment
	public LinkedList<LinkedList<Integer>> assigned;
	private HashSet<Integer> pure, unit, useless;
	private Set<Integer> provedformula, disprovedformula;
	private LinkedList<Integer> usedvar;
	private boolean normalized;
	private LinkedList<Pair<Integer, Character>> currentassign;
	public AdjacencyListFormula(int n, int fcount) {
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
			AdjacencyListClause d = this.formula.get(id);
			d.set(v, this, -1, id);
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
					// for a satisfied reason, we can anything other than a branching
					// variable
					if (lastassign.second != 'N' || isMax(lastassign.first)) { 
						r.literals.remove(lastassign.first);
					}
				} else {
					// for existential literal, things are a bit complicated
					if (lastassign.second == 'P' || lastassign.second == 'B') {
						r.literals.remove(lastassign.first);
					} else if (lastassign.second == 'U') {
						r.literals.remove(lastassign.first);
						for (Integer id : this.varToformula.get(Math.abs(v))) {
							AdjacencyListClause d = this.formula.get(id);
							if (d.hasUnit(this)) {
								List<Integer> contradict = d.getContradiction();
								for (Integer cc : contradict) {
									r.literals.add(-cc);
								}
								break;
							}
						}
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
		if (isMax(v)) {
			this.set(v, 'U');
		} else {
			this.set(-v, 'U');
		}
		return true;
	}
	
	private boolean pure_literal_elimination() {
		if (terminal()) return false;
		if (pure.isEmpty()) return false;
		int v = pure.iterator().next();
		pure.remove(v);
		if (isMax(v)) {
			this.set(v, 'P');
		} else {
			this.set(-v, 'P');
		}
		return true;
	}
	
	private void eliminate_useless_quantifier() {
		for (Integer id : this.useless) {
			this.dropquantifier(id);
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
				((AdjacencyListClause) c).incExist(1);
			}
		}
		
		formula.add((AdjacencyListClause) c);
		// add an empty clause
		if (c.isEmpty()) {
			this.disproved++;
		}
	}

	@Override
	public Quantifier peek() {
		if (normalized == false) {
			System.err.println("hasn't called normal!");
			System.exit(0);
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
			AdjacencyListClause d = this.formula.get(id);
			d.set(Math.abs(v), this, v > 0 ? 1 : 0, id);
			this.usedformula.get(Math.abs(v)).add(id);
		}
		
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
		for (int i = 1; i <= n; ++i) {
			if (block.hasQuantifier(i)) continue;
			this.addquantifier(new Quantifier(isMax(i), i));
		}
		
		for (int i = 1; i <= n; ++i) {
			if (this.getFreq(i) == 0) {
				useless.add(i);
			}
		}
		
		eliminate_useless_quantifier();
		this.setNormal();
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
					lv = Math.min(lv, target);
				}
			}
			
			if (target != 0 && cnt == 1 && lv > this.getLevel(target)) {
				this.addUnit(target);
			}
		}
		
		this.simplify();
		this.commit();
	}
	
	private boolean check(int v, HashSet<Integer> ass) {
		//System.out.println("----check------- " + v + " --------");
		//System.out.println("current assign " + ass);
		for (Integer id : this.varToformulainit.get(Math.abs(v))) {
			//System.out.println("formula with id= " + id);
			AdjacencyListClause d = this.formula.get(id);
			boolean in = false, ok = false;
			List<Integer> lit = d.getAll();
			for (Integer l : lit) {
				if (l == v) {
					in = true;
				}
				
				if (l != v && ass.contains(l)) {
					//System.out.println("contains assign " + l);
					ok = true;
				}
			}
			
			if (in && !ok) return false;
		}
		return true;
	}
	
	public Reason getReason() {
		int res = -1;
		HashSet<Integer> nonproved = new HashSet<>();
		if (this.disproved > 0) {
			res = 0;
		} else if (this.proved == this.fcount) {
			res = 1;
		} else {
			if (this.block.unicount == 0) {
				ISolver s = SolverFactory.newDefault();
				s.setTimeout(900);
				s.newVar(this.n + 1);
				s.setExpectedNumberOfClauses(this.fcount);
				for (AdjacencyListClause d : this.formula) {
					if (d.evaluate() != -1) continue;
					List<Integer> list = d.getLiteral();
					nonproved.addAll(d.getContradiction());
					int [] clause = list.stream().mapToInt(Integer::intValue).toArray();
					try {
						s.addClause(new VecInt(clause));
					} catch (ContradictionException e) {
						res = -2;
					}
				}
				
				try {
					boolean curr = s.isSatisfiable();
					if (curr) {
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
		
		Reason ret = new Reason();
		ret.satisfied = res == 1;
		// SAT solver is called
		if (res == 2) {
			for (Pair<Integer, Character> p : this.currentassign) {
				if (!isMax(p.first)) {
					ret.literals.add(p.first);
				}
			}	
		} else if (res == -2) {
			for (Pair<Integer, Character> p : this.currentassign) {
				if (isMax(p.first) && nonproved.contains(-p.first)) {
					ret.literals.add(p.first);
				}
			}
		} else {
			if (res == 1) {
				HashSet<Integer> ass = new HashSet<>();
				LinkedList<Integer> li = new LinkedList<>();
				for (Pair<Integer, Character> p : this.currentassign) {
					if (p.second != 'B') {
						ass.add(p.first);
					}
					if (!isMax(p.first)) {
						li.add(p.first);
					}
				}
				
				Iterator<Integer> iter = li.descendingIterator();
				while (iter.hasNext()) {
					int cand = iter.next();
					if (check(cand, ass)) {
						//System.out.println("check " + cand);
						iter.remove();
						ass.remove(cand);
					} else {
						//System.out.println("check fail " + cand);
					}
				}
				ret.literals.addAll(li);
			} else {
				if (!this.disprovedformula.isEmpty()) {
					int id = this.disprovedformula.iterator().next();
					for (Integer cc : this.formula.get(id).getContradiction()) {
						if (isMax(cc)) {
							ret.literals.add(-cc);
						}
					}
				}
			}
		}
		/*if (res == 0 || res == 1) {
			System.out.println(res + " " + ret.literals);
		} else {
			System.out.println("sat determined " + res);
		}*/
		return ret;
	}

	@Override
	public int evaluate() {
		if (this.disproved > 0) return 0;
		if (this.proved == this.fcount) return 1;
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
		
		return -1;
	}

	@Override
	public CnfExpression duplicate() {
		return this;
	}

}
