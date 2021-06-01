package utilstructure;
import java.util.Map;
import java.util.TreeMap;

public class MultiSet<T extends Comparable<T>> {
	Map<T, Integer> mp;
	public MultiSet() {
		this.mp = new TreeMap<>();
	}
	
	public void add(T val) {
		mp.put(val, mp.getOrDefault(val, 0) + 1);
	}
	
	public void erase(T val) {
		mp.remove(val);
	}
	
	public void removeone(T val) {
		if (mp.getOrDefault(val, 0) > 1) {
			mp.put(val, mp.get(val) - 1);
		} else {
			mp.remove(val);
		}
	}
	
	public int count(T val) {
		return mp.getOrDefault(val, 0);
	}
	
	public boolean contains(T val) {
		return count(val) > 0;
	}
}
