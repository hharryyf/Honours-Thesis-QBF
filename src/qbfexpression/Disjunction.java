package qbfexpression;

import java.util.List;

public interface Disjunction {
	public boolean hasvar(int val);
	public boolean contains(int val);
	public boolean isEmpty();
	public List<Integer> getLiteral();
	public List<Integer> getVariable();
	public List<Integer> getAll();
	public int getSize();
	public void add(int val);
	public int evaluate();
}
