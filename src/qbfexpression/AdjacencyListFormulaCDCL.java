package qbfexpression;

//import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import qbfsolver.ResultGenerator;
import utilstructure.Pair;

public class AdjacencyListFormulaCDCL extends AdjacencyListFormulaWithReason {
	public Reason conflict;
	public List<Reason> nogoods;
	public AdjacencyListFormulaCDCL(int n, int fcount) {
		super(n, fcount);
		this.conflict = new Conflict();
		this.learnedunit = new HashSet<>();
		this.nogoods = new ArrayList<>();
	}
	
	public boolean isOuter(int v) {
		return this.block.isOuter(v);
	}
	
	public void learn() throws IOException {
		if (((Conflict) conflict).counter == -1) {
			for (Reason rr : this.nogoods) {
				AdjacencyListClauseWithReason c = new AdjacencyListClauseWithReason();
				c.setLearn();
				for (Integer cc : rr.literals) {
					c.add(cc);
				}
				
				List<Integer> ret = c.getLiteral();
				for (int i = 0 ; i < ret.size(); ++i) {
					if (c.evaluate() == 1) {
						this.proved++;
						break;
					}
					int v = ret.get(i);
					this.updateCounter(v, 1);
					if (ret.size() == 1) {
						this.addUnit(v);
						System.out.println("must learn unit " + v);
					}
					if (v < 0) v = -v;
					varToformula.get(v).add(formula.size());
					varToformulainit.get(v).add(formula.size());
					if (isMax(v)) {
						((AdjacencyListClauseWithReason) c).incExist(1);
					}
				}
				
				formula.add((AdjacencyListClauseWithReason) c);
				System.out.println("learn " + c);
				if (c.isEmpty() || c.evaluate() == 0) {
					this.disproved++;
					System.err.println("try to insert an empty clause");
					System.out.println("UNSAT");
					System.exit(0);
				}
				this.fcount++;
			}
			ResultGenerator.learnpreprocess = true;
			this.simplify();
			this.commit();
			ResultGenerator.learnpreprocess = false;
		}
		this.conflict.literals.clear();
		this.nogoods.clear();
		((Conflict) conflict).counter = 0;
	}
	
	@Override
	public int evaluate() {
		if (this.disproved > 0) return 0;
		if (this.proved == this.fcount) return 1;
		return -1;
	}
	
	private void conflictresolve(int v) {
		if (v < 0) v = -v;
		while (!this.usedformula.get(v).isEmpty()) {
			int id = this.usedformula.get(v).pollLast();
			AdjacencyListClauseWithReason d = this.formula.get(id);
			d.set(v, this, -1, id);
		}
		
		Pair<Integer, Character> lastassign = super.currentassign.removeLast();
		if (this.conflict.satisfied) {
			return;
		} else {
			if (((Conflict) conflict).counter <= -1) return;
			//System.out.println("last assigned= " + lastassign.first + " " + lastassign.second);
			//System.out.println("conflict= " + this.conflict.literals);
			if (lastassign.second == 'P' || lastassign.second == 'B' || !isMax(lastassign.first)) return;
			if (lastassign.second == 'U') {
				if (this.conflict.literals.contains(-lastassign.first)) {
					boolean found = false;
					for (Integer id : this.varToformula.get(Math.abs(v))) {
						AdjacencyListClauseWithReason d = this.formula.get(id);
						if (d.hasUnit(this, lastassign.first)) {
							List<Integer> contradict = d.getAll();
							List<Integer> ureduct = new LinkedList<>();
							int lv = -1;
							for (Integer v1 : contradict) {
								if (this.learnedunit.contains(v1) || this.learnedunit.contains(-v1)) continue;
								if (this.isMax(v1)) {
									lv = Math.max(lv, this.getLevel(v1));
								}
							}
							
							for (Integer v1 : contradict) {
								if (this.learnedunit.contains(v1) || this.learnedunit.contains(-v1)) continue;
								if (isMax(v1) || this.getLevel(v1) < lv) {
									ureduct.add(v1);
								}
							}
							
							boolean bad = false;
							for (Integer cc : ureduct) {
								if ((cc.intValue() != lastassign.first.intValue()) && this.conflict.literals.contains(-cc)) {
									bad = true;
									//System.out.println(this.conflict.literals + " blocked by " + ureduct + " on literal " + cc);
									break;
								}
							}
							
							if (!bad) {
								found = true;
								// System.out.println("resolve " + ureduct + " " + this.conflict.literals);
								for (Integer cc : ureduct) {
									this.conflict.literals.add(cc);
								}
								
								this.conflict.literals.remove(-lastassign.first);
								this.conflict.literals.remove(lastassign.first);
								lv = -1;
								for (Integer v1 : this.conflict.literals) {
									if (this.isMax(v1)) {
										lv = Math.max(lv, this.getLevel(v1));
									}
								}
								
								Iterator<Integer> iter = this.conflict.literals.iterator();
								while (iter.hasNext()) {
									int v1 = iter.next();
									if (!isMax(v1) && this.getLevel(v1) > lv) {
										iter.remove();
									}
								}
								
								break;
							}
						}
						
						if (found) break;
					}
					
					if (!found) {
						if (((Conflict) conflict).counter > 0) {
							((Conflict) conflict).counter = -1;
							if (this.conflict.literals.size() < 16) {
								this.nogoods.add(conflict.duplicate());
							}
						} else {
							((Conflict) conflict).counter = -2;
						}
					} else {
						((Conflict) conflict).counter += 1;
						if (this.conflict.literals.size() < 16) {
							this.nogoods.add(conflict.duplicate());
						}
					}
					
				}
			} else {
				if (((Conflict) conflict).counter > 0) {
					((Conflict) conflict).counter = -1;
					if (this.conflict.literals.size() < 16) {
						this.nogoods.add(conflict.duplicate());
					}
				} 
			}
		}
	}
	
	@Override
	public void undo() {
		if (!this.assigned.isEmpty()) {
			LinkedList<Integer> last = assigned.pollLast();
			while (!last.isEmpty()) {
				int it = last.pollLast();
				it = Math.abs(it);
				this.addquantifier(this.block.quantifiers[it]);
				this.conflictresolve(it);
			}
		}
		super.pure.clear();
		super.unit.clear();
		super.useless.clear();
	}
	
	public void getConflict() {
		this.conflict.literals.clear();
		if (!super.disprovedformula.isEmpty()) {
			this.nogoods.clear();
			this.conflict.satisfied = false;
			Iterator<Integer> biter = this.disprovedformula.iterator();
			int id = biter.next();
			for (Integer cc : this.formula.get(id).getAll()) {
				if (this.learnedunit.contains(cc) || this.learnedunit.contains(-cc)) continue;
				this.conflict.literals.add(cc);
			}
			((Conflict) this.conflict).counter = 0;
		} else {
			this.conflict.satisfied = true;
		}
	}
}
