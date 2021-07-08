package qbfsolver;

import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

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
        		if (args.length == 1) {
        			p.preprocess();
        			fo = rd.read(0);
        			Solver s = new QDLLRBJ();
        			ret.setTruth(s.solve(fo));
        		} else {
        			p.preprocess();
        			fo = rd.read(0);
        			System.out.println(fo.getClass());
        			Solver s = new DeepPNSWithReason();
        			s.solve(fo);
        		}	
        		return ResultGenerator.getInstance();
            });

            System.out.println(f.get(30000, TimeUnit.SECONDS));
            
        } catch (final TimeoutException e) {
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
