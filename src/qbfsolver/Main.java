package qbfsolver;

import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import qbfefficient.TwoWatchedLiteralFormula;
import qbfexpression.CnfExpression;

public class Main {

	public static void main(String[] args) throws InterruptedException, ExecutionException {
		final ExecutorService service = Executors.newSingleThreadExecutor();
        try {
                final Future<Object> f = service.submit(() -> {
                QdimacsFilePreprocessor p = new QdimacsFilePreprocessor(); 
            	QdimacFileReader rd = new QdimacFileReader();
        		CnfExpression fo;
        		Result ret = ResultGenerator.getInstance();
        		if (args.length == 0) {
        			final long start = System.currentTimeMillis();
        			p.preprocess();
        			fo = rd.read(0);
        			Solver s = new QDLLRBJ();
        			boolean r = s.solve(fo);
        			ret.setTruth(r);
        			final long end = System.currentTimeMillis();
        			long cnt = TwoWatchedLiteralFormula.setcount, cnt2 = TwoWatchedLiteralFormula.clause_iter;
        			System.out.println("#branching= " + ResultGenerator.getInstance().getIteration() + " #ass= " 
        			              + cnt + " #clause iterate= " + cnt2 +
        			              "\nclause iterated per ass= " + (1.0 * cnt2 / (cnt + 1)) + 
        			              "\ntotal time " + (1.0 * (end-start) / 1000));
        		} else {
        			p.preprocess();
        			fo = rd.read(0);
        			System.out.println(fo.getClass());
        			Solver s = new DeepPNSWithReason();
        			s.solve(fo);
        		}	
        		return ResultGenerator.getInstance();
            });

            System.out.println(f.get(900, TimeUnit.SECONDS));
            
        } catch (final TimeoutException e) {
        	long cnt = TwoWatchedLiteralFormula.setcount, cnt2 = TwoWatchedLiteralFormula.clause_iter;
			System.out.println("#branching= " + ResultGenerator.getInstance().getIteration() + " #ass= " 
			              + cnt + " #clause iterate= " + cnt2 +
			              "\nclause iterated per ass= " + (1.0 * cnt2 / (cnt + 1)));
            System.out.println("UNSOLVED NA");
            service.shutdown();
            System.exit(0);
        } catch (final Exception e) {
            throw new RuntimeException(e);
        } finally {
        	service.shutdown();
        }

	}

}
