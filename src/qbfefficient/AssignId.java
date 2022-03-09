package qbfefficient;

public class AssignId implements Comparable<AssignId> {
	public int dimension;
	public char type;
	public int id;
	
	public AssignId(int d, char t, int id) {
		this.dimension = d;
		this.type = t;
		this.id = id;
	}
	
	@Override
	public int compareTo(AssignId arg0) {
		if (dimension != arg0.dimension) return (new Integer(dimension)).compareTo(new Integer(arg0.dimension)); 
		if (type != arg0.type) return (new Character(type)).compareTo(new Character(arg0.type));
		return (new Integer(id)).compareTo(new Integer(arg0.id));
	}
	
	public String toString() {
		return "(" + dimension + ", " + type + ", " + id + ")";
	}
	
}
