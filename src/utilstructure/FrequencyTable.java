package utilstructure;

import java.util.TreeSet;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.TreeMap;

public class FrequencyTable<T extends Comparable<T>> {
	private TreeMap<Integer, TreeSet<T>> freqToitem;
	private TreeMap<T, Integer> itemTofreq;
	public FrequencyTable() {
		this.freqToitem = new TreeMap<>();
		this.itemTofreq = new TreeMap<>();
	}
	
	/**
	 * precondition: the item is not in the frequency table
	 * otherwise, do nothing
	 * @param item
	 */
	public void insert(T item) {
		if (itemTofreq.containsKey(item)) return;
		itemTofreq.put(item, 0);
		if (!freqToitem.containsKey(0)) {
			freqToitem.put(0, new TreeSet<>());
		}
		freqToitem.get(0).add(item);
	}
	
	/**
	 * precondition: the item is in the frequency table
	 * otherwise, do nothing
	 * @param item
	 */
	
	public void remove(T item) {
		if (!itemTofreq.containsKey(item)) return;
		int freq = itemTofreq.get(item);
		itemTofreq.remove(item);
		freqToitem.get(freq).remove(item);
		if (freqToitem.get(freq).isEmpty()) {
			freqToitem.remove(freq);
		}
	}
	
	/**
	 * 
	 * @param item
	 * @return true if item is in the map itemTofreq
	 */
	
	public boolean contains(T item) {
		return itemTofreq.containsKey(item);
	}
	
	/**
	 * precondition: item is in the frequency table
	 * @param item 
	 * @param freq
	 */
	
	public void updateFreq(T item, int freq) {
		if (freq < 0) return;
		if (!this.contains(item)) {
			this.insert(item);
		}
		int fq = itemTofreq.get(item);
		itemTofreq.put(item, freq);
		TreeSet<T> curr = freqToitem.get(fq);
		curr.remove(item);
		if (curr.isEmpty()) {
			freqToitem.remove(fq);
		}
		if (!freqToitem.containsKey(freq)) {
			freqToitem.put(freq, new TreeSet<>());
		}
		freqToitem.get(freq).add(item);
	}
	
	/**
	 * 
	 * @return the number of distinct items in the frequency table
	 */
	public int size() {
		return itemTofreq.size();
	}
	
	public boolean isEmpty() {
		return itemTofreq.isEmpty();
	}
	
	public List<T> peekTop(int count) {
		count = Math.max(1, Math.min(4, count));
		List<T> ret = new ArrayList<>();
		Iterator<T> iter = freqToitem.lastEntry().getValue().descendingIterator();
		while (iter.hasNext()) {
			ret.add(iter.next());
			if (ret.size() == count) break;
		}
		return ret;
	}
	
	public String toString() {
		return this.freqToitem.toString() + "\n" + this.itemTofreq.toString();
	}
}
