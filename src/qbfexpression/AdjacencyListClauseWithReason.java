package qbfexpression;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import utilstructure.Pair;

public class AdjacencyListClauseWithReason implements Disjunction {

	private int existcount = 0;
	private int proved = 0, disproved = 0;
	private HashSet<Integer> checkedliterals;
	// [literal, value (-1, 0, 1), 0 means -literal, 1 means good, -1 means pending]
	protected List<Pair<Integer, Integer>> literal;
	private boolean trivial = false;
	// this unassigned stored all the unassigned literals at the point the formula changed state
	// from -1 -> 0/1
	private List<Integer> unassigned;
	public AdjacencyListClauseWithReason() {
		this.literal = new ArrayList<>();
		this.existcount = 0;
		this.disproved = this.proved = 0;
		this.unassigned = new ArrayList<>();
		this.checkedliterals = new HashSet<>();
	}
	
	public int getExist() {
		return this.existcount;
	}
	
	public void incExist(int val) {
		this.existcount += val;
	}

	@Override
	public boolean hasvar(int val) {
		if (isEmpty()) return false;
		int i;
		for (i = 0 ; i < literal.size(); ++i) {
			if (val == Math.abs(literal.get(i).first)) {
				return true;
			}
		}
		
		return false;
	}

	
	
	@Override
	public boolean contains(int val) {
		if (evaluate() != -1) return false;/*
		int i;
		for (i = 0 ; i < literal.size(); ++i) {
			if (val == literal.get(i).first) {
				return true;
			}
		}
		
		return false;*/
		return this.checkedliterals.contains(val);
	}



	@Override
	public boolean isEmpty() {
		return this.literal.size() == 0;
	}



	@Override
	public List<Integer> getLiteral() {
		List<Integer> ret = new ArrayList<>();
		for (Pair<Integer, Integer> p : this.literal) {
			if (p.second == -1) {
				ret.add(p.first);
			}
		}
		return ret;
	}


    public List<Integer> getContradiction() {
    	List<Integer> ret = new ArrayList<>();
    	for (Pair<Integer, Integer> p : this.literal) {
    		if (p.second == 0) {
    			ret.add(p.first);
    		}
    	}
    	return ret;
    }
	
	@Override
	public List<Integer> getVariable() {
		List<Integer> ret = new ArrayList<>();
		for (Pair<Integer, Integer> p : this.literal) {
			if (p.second == -1) {
				ret.add(Math.abs(p.first));
			}
		}
		return ret;
	}



	@Override
	public int getSize() {
		return this.literal.size();
	}



	@Override
	public void add(int val) {
		if (contains(-val)) {
			this.trivial = true;
			return;
		}
		
		if (contains(val)) {
			// System.out.println("duplicate " + val);
			return;
		}
		
		this.checkedliterals.add(val);
		this.literal.add(new Pair<>(val, -1));
	}
    
	protected boolean hasUnit(AdjacencyListFormulaWithReason f, int v) {
		if (!this.contains(v)) return false;
		if (evaluate() != -1 || this.existcount != 1) return false;
		for (Pair<Integer, Integer> p : this.literal) {
			if (p.second != 0 && !f.isMax(p.first) && (f.getLevel(p.first) < f.getLevel(v))) {
				return false;
			}
		}
			
		return true;
	}
	
    public void set(int v, AdjacencyListFormulaWithReason f, int val, int id) {
		if (v < 0) {
			System.err.println("negative v assigned to formula " + id + " !");
			System.exit(1);
		}
		
		int before = evaluate();
		if (val == -1) {
			for (Pair<Integer, Integer> p : this.literal) {
				if (Math.abs(p.first) == v) {
					if (p.second == -1) {
						continue;
					}
					
					if (p.second == 0) {
						this.disproved--;
					} else {
						this.proved--;
					}
					
					if (f.isMax(v)) {
						this.existcount++;
					}
					p.second = -1;
					break;
				}
			}
		} else {
			for (Pair<Integer, Integer> p : this.literal) {
				if (Math.abs(p.first) == v) {
					int w = val == 1 ? v : -v;
					if (w == p.first) {
						p.second = 1;
						this.proved++;
					} else {
						p.second = 0;
						this.disproved++;
					}
					
					if (f.isMax(v)) {
						this.existcount--;
					}
					break;
				}
			}
		}
		
		int after = evaluate();
		if (before != after) {
			if (val == -1) {
				if (before == -1) {
					System.err.println("something wrong with the logic! type-1");
					System.exit(1);
				}
				for (Integer curr : this.unassigned) {
					f.updateCounter(curr, 1);
				}
				this.unassigned.clear();
				f.addProved(id, false);
				if (before == 1) {
					f.incProved(-1);
				} else {
					f.incDisproved(-1);
					f.addDisprove(id, false);
				}
			} else {
				if (after == -1) {
					System.err.println("something wrong with the logic! type-2");
					System.exit(1);
				}
				
				for (Pair<Integer, Integer> p : this.literal) {
					if (p.second == -1) {
						this.unassigned.add(p.first);
						f.updateCounter(p.first, -1);
					}
				}
				
				f.addProved(id, true);
				if (after == 1) {
					f.incProved(1);
				} else {
					f.incDisproved(1);
					f.addDisprove(id, true);
				}
			}
		}
		
		// we consider to do unit propagation
		
		if (val != -1 && evaluate() == -1 && this.existcount == 1) {
			int target = 0, lv = Integer.MAX_VALUE;
			for (Pair<Integer, Integer> p : this.literal) {
				if (p.second == -1 && f.isMax(p.first)) {
					target = p.first;
				} 
				
				if (p.second == -1 && !f.isMax(p.first)) {
					lv = Math.min(lv, f.getLevel(p.first));
				}
			}
			
			if (target == 0) {
				System.err.println("bad");
				System.exit(0);
			}
			
			if (f.getLevel(target) < lv) {
				f.addUnit(target);
			}
		}
	}



	@Override
	public int evaluate() {
		if (this.trivial) return 1;
		if (this.proved > 0) return 1;
		if (this.existcount == 0) return 0;
		if (this.disproved == this.literal.size()) return 0;
		return -1;
	}

	public String toString() {
		return "{" + this.literal.toString() + " " + this.disproved + " " + this.proved + " " + this.existcount + " " + this.evaluate() + "}";
	}

	@Override
	public List<Integer> getAll() {
		List<Integer> ret = new ArrayList<>();
		for (Pair<Integer, Integer> p : this.literal) {
			ret.add(p.first);
		}
		return ret;
	}

}
