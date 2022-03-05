package qbfefficient;

public class GlobalReason {
	private static ConflictSolution reason;
	public static ConflictSolution GetReason() {
		if (reason == null) {
			reason = new PNSLearnReason(false);
		}
		return reason;
	}
	
	public static void setReason(PNSLearnReason r) {
		reason = r;
	}
}
