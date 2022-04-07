package qbfefficient;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashSet;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import qbfexpression.Quantifier;
import qbfsolver.Result;
import qbfsolver.ResultGenerator;
import utilstructure.Pair;

public class QDPLL {
	protected static String lm = new String("QDPLL");
	protected int pruneLevel = -1;
	public Pair<ConflictSolution, Boolean> qcdcl(TwoWatchedLiteralFormula f, int d) {
		Result rr = ResultGenerator.getInstance();
		rr.setIteration(1 + rr.getIteration());
		if (f == null) return null;
		int ret = f.evaluate();
		Random rd = new Random();
		int idx = rd.nextInt(2) == 1 ? 1 : -1;
		if (!TwoWatchedLiteralFormula.rand) idx = 1;
		if (ret == 0) {
			return new Pair<>(f.getReason(), false);
		}
		if (ret == 1) return new Pair<>(f.getReason(), true);
		Quantifier q = f.peek();
		if (q.isMax()) {
			f.set(q.getVal() * idx);
			f.simplify();
			Pair<ConflictSolution, Boolean> res = qcdcl(f, d + 1);
			if (res.second) {
				TwoWatchedLiteralFormula.truecount++;
			} else {
				TwoWatchedLiteralFormula.falsecount++;
			}
			f.undo(res.first);
			if (res.second || !res.first.contains(-q.getVal() * idx)) {
				if (!res.second && !res.first.contains(-q.getVal() * idx)) {
					TwoWatchedLiteralFormula.prunE++;
			    	MyLog.log(lm, pruneLevel, "p-E ", q.getVal() * idx, " d=", d);
			    }
				return res;
			}
			f.set(-q.getVal() * idx);
			f.simplify();
			Pair<ConflictSolution, Boolean> other = qcdcl(f, d + 1);
			f.undo(other.first);
			if (!other.second && other.first.contains(q.getVal() * idx)) {
			    other.first.resolve(res.first, q.getVal(), f);
			    TwoWatchedLiteralFormula.rescount++;
			}
			
			if (other.second) {
				TwoWatchedLiteralFormula.truecount++;
			} else {
				TwoWatchedLiteralFormula.falsecount++;
			}
			
			return other;
		}
		
		f.set(q.getVal() * idx);
		f.simplify();
		Pair<ConflictSolution, Boolean> res = qcdcl(f, d + 1);
		
		if (res.second) {
			TwoWatchedLiteralFormula.truecount++;
		} else {
			TwoWatchedLiteralFormula.falsecount++;
		}
		
		f.undo(res.first);
		if (!res.second || !res.first.contains(q.getVal() * idx)) {
		    if (res.second && !res.first.contains(q.getVal() * idx)) {
		    	TwoWatchedLiteralFormula.prunU++;
		    	MyLog.log(lm, pruneLevel, "p-U ", q.getVal() * idx, " d=", d);
		    }
		    
		    MyLog.log(lm, 3, "reason: ", res, " branching variable: ", q.getVal() * idx, " type= ", res.first.isSolution());
			return res;
		}
		f.set(-q.getVal() * idx);
		f.simplify();
		Pair<ConflictSolution, Boolean> other = qcdcl(f, d + 1);
		f.undo(other.first);
		if (other.second && other.first.contains(-q.getVal() * idx)) {
			MyLog.log(lm,TwoWatchedLiteralFormula.res_level, "resolve", other, "and", res);
			other.first.resolve(res.first, q.getVal() * idx, f);
			MyLog.log(lm, TwoWatchedLiteralFormula.res_level, "get", other);
			TwoWatchedLiteralFormula.rescount++;
		}
		
		MyLog.log(lm, 3, "reason: ", other, " branching variable: ", -q.getVal() * idx, " type= ", other.first.isSolution());
		if (other.second) {
			TwoWatchedLiteralFormula.truecount++;
		} else {
			TwoWatchedLiteralFormula.falsecount++;
		}
		return other;
	}
	
	public Pair<ConflictSolution, Boolean> cdclsbj(TwoWatchedLiteralFormula f, int d) {
		Result rr = ResultGenerator.getInstance();
		rr.setIteration(1 + rr.getIteration());
		if (f == null) return null;
		int ret = f.evaluate();
		Random rd = new Random();
		int idx = rd.nextInt(2) == 1 ? 1 : -1;
		if (!TwoWatchedLiteralFormula.rand) idx = 1;
		if (ret == 0) {
			return new Pair<>(f.getReason(), false);
		}
		if (ret == 1) return new Pair<>(f.getReason(), true);
		Quantifier q = f.peek();
		if (q.isMax()) {
			f.set(q.getVal() * idx);
			f.simplify();
			Pair<ConflictSolution, Boolean> res = cdclsbj(f, d + 1);
			if (res.second) {
				TwoWatchedLiteralFormula.truecount++;
			} else {
				TwoWatchedLiteralFormula.falsecount++;
			}
			f.undo(res.first);
			if (res.second || !res.first.contains(-q.getVal() * idx)) {
				if (!res.second && !res.first.contains(-q.getVal() * idx)) {
					TwoWatchedLiteralFormula.prunE++;
			    	MyLog.log(lm, pruneLevel, "p-E ", q.getVal() * idx, " d=", d);
				}
				return res;
			}
			f.set(-q.getVal() * idx);
			f.simplify();
			Pair<ConflictSolution, Boolean> other = cdclsbj(f, d + 1);
			f.undo(other.first);
			if (!other.second && other.first.contains(q.getVal() * idx)) {
			    other.first.resolve(res.first, q.getVal(), f);
			    TwoWatchedLiteralFormula.rescount++;
			}
			
			if (other.second) {
				TwoWatchedLiteralFormula.truecount++;
			} else {
				TwoWatchedLiteralFormula.falsecount++;
			}
			return other;
		}
		
		f.set(q.getVal() * idx);
		f.simplify();
		Pair<ConflictSolution, Boolean> res = cdclsbj(f, d + 1);
		if (res.second) {
			TwoWatchedLiteralFormula.truecount++;
		} else {
			TwoWatchedLiteralFormula.falsecount++;
		}
		f.undo(res.first);
		if (!res.second || !res.first.contains(q.getVal() * idx)) {
		    if (res.second && !res.first.contains(q.getVal() * idx)) {
		    	TwoWatchedLiteralFormula.prunU++;
		    	MyLog.log(lm, pruneLevel, "p-U ", q.getVal() * idx, " d=", d);
		    }
			return res;
		}
		f.set(-q.getVal() * idx);
		f.simplify();
		Pair<ConflictSolution, Boolean> other = cdclsbj(f, d + 1);
		f.undo(other.first);
		if (other.second && other.first.contains(-q.getVal() * idx)) {
		    other.first.resolve(res.first, q.getVal() * idx, f);
		    TwoWatchedLiteralFormula.rescount++;
		}
		
		if (other.second) {
			TwoWatchedLiteralFormula.truecount++;
		} else {
			TwoWatchedLiteralFormula.falsecount++;
		}
		return other;
	}
	
	public Pair<ConflictSolution, Boolean> backjumping(TwoWatchedLiteralFormula f, int d) {
		Result rr = ResultGenerator.getInstance();
		rr.setIteration(1 + rr.getIteration());
		if (f == null) return null;
		int ret = f.evaluate();
		if (ret == 0) {
			return new Pair<>(f.getReason(), false);
		}
		if (ret == 1) return new Pair<>(f.getReason(), true);
		Random rd = new Random();
		int idx = rd.nextInt(2) == 1 ? 1 : -1;
		if (!TwoWatchedLiteralFormula.rand) idx = 1;
		Quantifier q = f.peek();
		if (q.isMax()) {
			f.set(idx * q.getVal());
			f.simplify();
			Pair<ConflictSolution, Boolean> res = backjumping(f, d + 1);
			f.undo(res.first);
			if (res.second || !res.first.contains(q.getVal())) {
				if (!res.second && !res.first.contains(q.getVal())) {
					TwoWatchedLiteralFormula.prunE++;
					MyLog.log(lm, pruneLevel, "p-E ", q.getVal(), " d=", d);
				}
				res.first.drop(null, q.getVal());
				return res;
			}
			f.set(-idx * q.getVal());
			f.simplify();
			Pair<ConflictSolution, Boolean> other = backjumping(f, d + 1);
			f.undo(other.first);
			if (!other.second && other.first.contains(-q.getVal())) {
			    other.first.resolve(res.first, q.getVal(), f);
			    TwoWatchedLiteralFormula.rescount++;
			}
			return other;
		}
		
		f.set(idx * q.getVal());
		f.simplify();
		Pair<ConflictSolution, Boolean> res = backjumping(f, d + 1);
		f.undo(res.first);
		if (!res.second || !res.first.contains(q.getVal())) {
		    if (res.second && !res.first.contains(q.getVal())) {
		    	TwoWatchedLiteralFormula.prunU++;
		    	MyLog.log(lm, pruneLevel, "p-U ", q.getVal(), " d=", d);
		    }
			res.first.drop(null, q.getVal());
			return res;
		}
		f.set(-idx * q.getVal());
		f.simplify();
		Pair<ConflictSolution, Boolean> other = backjumping(f, d + 1);
		f.undo(other.first);
		if (other.second && other.first.contains(-q.getVal())) {
		    other.first.resolve(res.first, q.getVal(), f);
		    TwoWatchedLiteralFormula.rescount++;
		}
		return other;
	}
	
	public boolean baseline(TwoWatchedLiteralFormula f) {
		Result rr = ResultGenerator.getInstance();
		rr.setIteration(1 + rr.getIteration());
		if (f == null) return true;
		int ret = f.evaluate();
		if (ret == 0) {
			f.getReason();
			return false;
		}
		if (ret == 1) return true;
		Quantifier q = f.peek();
		if (q.isMax()) {
			f.set(q.getVal());
			f.simplify();
			boolean res = baseline(f);
			f.undo(null);
			if (res) {
				return true;
			}
			f.set(-q.getVal());
			f.simplify();
			res = baseline(f);
			f.undo(null);
			return res;
		}
		
		f.set(q.getVal());
		f.simplify();
		boolean res = baseline(f);
		f.undo(null);
		if (!res) {
			return false;
		}
		f.set(-q.getVal());
		f.simplify();
		res = baseline(f);
		f.undo(null);
		return res;
	}
	
	public static void main(String args[]) throws FileNotFoundException, InterruptedException, ExecutionException {
		
		TwoWatchedLiteralConstructor reader = new TwoWatchedLiteralConstructor();
		TwoWatchedLiteralFormula ret = reader.construct();
		MyLog.log(lm, 1, "#################### Timer Start ##################");
		final long start = System.currentTimeMillis();
		final ExecutorService service = Executors.newSingleThreadExecutor();
		try {
			QDPLL solver = new QDPLL();
			
			final Future<Boolean> f = service.submit(()->{
				boolean res = false;
				
				Set<String> set = new HashSet<>();
				
				for (int i = 0 ; i < args.length; ++i) {
					set.add(args[i]);
				}
				
				if (set.contains("backjumping")) {
					TwoWatchedLiteralFormula.solvertype = TwoWatchedLiteralFormula.Method.BJ;
				} else if (set.contains("cdclsbj")) {
					TwoWatchedLiteralFormula.solvertype = TwoWatchedLiteralFormula.Method.CDCLSBJ;
				} else {
					TwoWatchedLiteralFormula.solvertype = TwoWatchedLiteralFormula.Method.QCDCL;
				}
				
				if (set.contains("pure")) {
					TwoWatchedLiteralFormula.PLErule = true;
				} else {
					TwoWatchedLiteralFormula.PLErule = false;
				}
				
				if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BT) {
					res = solver.baseline(ret);
				} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.BJ) {
					res = solver.backjumping(ret, 0).second;
				} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.CDCLSBJ) {
					res = solver.cdclsbj(ret, 0).second;
				} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.QCDCL) {
					MyLog.log(lm, 1, "clause_len_limit= ", TwoWatchedLiteralFormula.max_clause_length, "cube_len_limit= ", TwoWatchedLiteralFormula.max_cube_length);
					res = solver.qcdcl(ret, 0).second;
				} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PLPRE_QCDCL) {
					QDeepPNS solve = new QDeepPNS();
					TwoWatchedLiteralFormula.preprocess = true;
					TwoWatchedLiteralFormula.solvertype = TwoWatchedLiteralFormula.Method.PL;
					int re = solve.deeppnsqcdcl_pre(ret);
					if (re == 0) {
						return false;
					} else if (re == 1) {
						return true;
					}
					
					try {
						FileWriter myWriter = new FileWriter("process.txt");
						System.out.println("finish pns - preprocessing");
						myWriter.write(ret.toString());
						myWriter.close();
					} catch (IOException e) {
						e.printStackTrace();
					}
					
					TwoWatchedLiteralFormula.preprocess = false;
					TwoWatchedLiteralFormula.solvertype = TwoWatchedLiteralFormula.Method.QCDCL;
					TwoWatchedLiteralFormula ret2 = reader.construct("process.txt");
					res = solver.qcdcl(ret2, 0).second;
					
				} else if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PLPRE_BJ) {
					QDeepPNS solve = new QDeepPNS();
					TwoWatchedLiteralFormula.preprocess = true;
					TwoWatchedLiteralFormula.solvertype = TwoWatchedLiteralFormula.Method.PL;
					int re = solve.deeppnsqcdcl_pre(ret);
					if (re == 0) {
						return false;
					} else if (re == 1) {
						return true;
					}
					
					try {
						FileWriter myWriter = new FileWriter("process.txt");
						System.out.println("finish pns - preprocessing");
						myWriter.write(ret.toString());
						myWriter.close();
					} catch (IOException e) {
						e.printStackTrace();
					}
					
					TwoWatchedLiteralFormula.preprocess = false;
					TwoWatchedLiteralFormula.solvertype = TwoWatchedLiteralFormula.Method.BJ;
					TwoWatchedLiteralFormula ret2 = reader.construct("process.txt");
					res = solver.backjumping(ret2, 0).second;
					
				} else {
					MyLog.log(lm, 0, "Please select the correct solver");
				}
				return res;
			});
			
			
			
			boolean res = f.get(TwoWatchedLiteralFormula.time_limit, TimeUnit.SECONDS);
			final long end = System.currentTimeMillis();
			long cnt = TwoWatchedLiteralFormula.clause_iter, cnt2 = TwoWatchedLiteralFormula.setcount;
			MyLog.log(lm, 1, "#branching= " + ResultGenerator.getInstance().getIteration() + " #ass= " 
		              + cnt2 + " #clause iterate= " + cnt);
			MyLog.log(lm, 1, "#bcp= ", TwoWatchedLiteralFormula.bcpcount, "#ple= ", TwoWatchedLiteralFormula.plecount);
			MyLog.log(lm, 1, "nclause iterated per ass= " + (1.0 * cnt / (cnt2 + 1))); 
			MyLog.log(lm, 1, "Existential Pruning= ", TwoWatchedLiteralFormula.prunE, " Universal Pruning: ", TwoWatchedLiteralFormula.prunU, "number of resolutions", TwoWatchedLiteralFormula.rescount, "total SAT terminal nodes: ", TwoWatchedLiteralFormula.trueterminal, "total UNSAT terminal nodes: ", TwoWatchedLiteralFormula.falseterminal);
			MyLog.log(lm, 1, "#prun/#branch= ", 1.0*(TwoWatchedLiteralFormula.prunE+TwoWatchedLiteralFormula.prunU)/ResultGenerator.getInstance().getIteration());
			MyLog.log(lm, 1, "total time " + (1.0 * (end-start) / 1000));
		    if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.QCDCL || TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.CDCLSBJ 
		    		|| TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.PL) {
		    	MyLog.log(lm, 1, "total SAT nodes: ", TwoWatchedLiteralFormula.truecount, " total UNSAT nodes: ", TwoWatchedLiteralFormula.falsecount);
		    	MyLog.log(lm, 1, "#learned clause= ", ret.tolLearnClause(), " #learned cube= ", ret.tolLearnCube());
		    } 
		    MyLog.log(lm, 1, "#################### EXIT SUCCESS ##################");
		    System.out.println((res ? "SAT" : "UNSAT"));
		}  catch (final TimeoutException e) {
			final long end = System.currentTimeMillis();
			long cnt = TwoWatchedLiteralFormula.clause_iter, cnt2 = TwoWatchedLiteralFormula.setcount;
			MyLog.log(lm, 1, "#branching= " + ResultGenerator.getInstance().getIteration() + " #ass= " 
		              + cnt2 + " #clause iterate= " + cnt);
			MyLog.log(lm, 1, "#bcp= ", TwoWatchedLiteralFormula.bcpcount, "#ple= ", TwoWatchedLiteralFormula.plecount);
			MyLog.log(lm, 1, "nclause iterated per ass= " + (1.0 * cnt / (cnt2 + 1))); 
			MyLog.log(lm, 1, "Existential Pruning= ", TwoWatchedLiteralFormula.prunE, " Universal Pruning: ", TwoWatchedLiteralFormula.prunU, "number of resolutions", TwoWatchedLiteralFormula.rescount, "total SAT terminal nodes: ", TwoWatchedLiteralFormula.trueterminal, "total UNSAT terminal nodes: ", TwoWatchedLiteralFormula.falseterminal);
			MyLog.log(lm, 1, "#prun/#branch= ", 1.0*(TwoWatchedLiteralFormula.prunE+TwoWatchedLiteralFormula.prunU)/ResultGenerator.getInstance().getIteration());
			MyLog.log(lm, 1, "total time " + (1.0 * (end-start) / 1000));
		    if (TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.QCDCL || TwoWatchedLiteralFormula.solvertype == TwoWatchedLiteralFormula.Method.CDCLSBJ) {
		    	MyLog.log(lm, 1, "total SAT nodes: ", TwoWatchedLiteralFormula.truecount, " total UNSAT nodes: ", TwoWatchedLiteralFormula.falsecount);
		    	MyLog.log(lm, 1, "#learned clause= ", ret.tolLearnClause(), " #learned cube= ", ret.tolLearnCube());
		    }
			MyLog.log(lm, 1, "#################### TIME OUT ##################");
			System.out.println("UNSOLVED");
			System.exit(0);
		} catch (final Exception e) {
            throw new RuntimeException(e);
        } finally {
        	service.shutdown();
        }
		
	}
}
