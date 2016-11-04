package sensing;

import java.awt.Color;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.HashMap;
import java.util.Map;
import java.util.Vector;
import java.util.logging.Level;

import org.metacsp.framework.ConstraintNetwork;
import org.metacsp.framework.Variable;
import org.metacsp.utility.logging.MetaCSPLogging;

import dispatching.FluentDispatchingFunction;
import examples.chimp.TestRACEDomain;
import fluentSolver.Fluent;
import fluentSolver.FluentNetworkSolver;
import htn.HTNMetaConstraint;
import htn.HTNPlanner;
import htn.TaskApplicationMetaConstraint.markings;
import hybridDomainParsing.DomainParsingException;
import hybridDomainParsing.HybridDomain;
import hybridDomainParsing.ProblemParser;
import unify.CompoundSymbolicVariableConstraintSolver;

public class TestFluentDispatching {

	public static void main(String[] args) {
		
		// init planner
		ProblemParser pp = new ProblemParser("problems/test_m_drive_robot_1.pdl");

		HybridDomain domain;
		try {
			domain = new HybridDomain("domains/ordered_domain.ddl");
		} catch (DomainParsingException e) {
			e.printStackTrace();
			return;
		}
		int[] ingredients = new int[] {1, domain.getMaxArgs()};
		String[][] symbols = new String[2][];
		symbols[0] =  domain.getPredicateSymbols();
		symbols[1] = pp.getArgumentSymbols();
		Map<String, String[]> typesInstancesMap = pp.getTypesInstancesMap();
		//+++
		
		HTNPlanner planner = new HTNPlanner(0,  600000,  0, symbols, ingredients);
		planner.setTypesInstancesMap(typesInstancesMap);
		
		FluentNetworkSolver fluentSolver = (FluentNetworkSolver)planner.getConstraintSolvers()[0];
		pp.createState(fluentSolver, domain);
		((CompoundSymbolicVariableConstraintSolver) fluentSolver.getConstraintSolvers()[0]).propagateAllSub();
		
		try {
			TestRACEDomain.initPlanner(planner, domain);
		} catch (DomainParsingException e) {
			System.out.println("Error while parsing domain: " + e.getMessage());
			e.printStackTrace();
			return;
		}
		
		MetaCSPLogging.setLevel(planner.getClass(), Level.FINEST);
		MetaCSPLogging.setLevel(HTNMetaConstraint.class, Level.FINEST);
//		MetaCSPLogging.setLevel(Level.INFO);
		
		planner.createInitialMeetsFutureConstraints();
		plan(planner, fluentSolver);
		
		// Add another task
		String name = "move_object(milkPot1 placingAreaNorthLeftTable2)";
		String component;
		if (name.startsWith("!")) {
			component = "Activity";
		} else {
			component = "Task";
		}
		Variable var = fluentSolver.createVariable(component);
		((Fluent) var).setName(name);
		var.setMarking(markings.UNPLANNED);
		
//		planner.clearResolvers();
		plan(planner, fluentSolver);
		
		TestRACEDomain.extractPlan(fluentSolver);
		
		// Dispatch the plan
		System.out.println("Starting Dispatching");
		
		FluentConstraintNetworkAnimator animator = new FluentConstraintNetworkAnimator(fluentSolver, 1000);
		
		final Vector<Fluent> executingActs = new Vector<Fluent>();
		
		FluentDispatchingFunction df = new FluentDispatchingFunction("Activity") {
			
			@Override
			public boolean skip(Fluent act) {
				// TODO Auto-generated method stub
				return false;
			}
			
			@Override
			public void dispatch(Fluent act) {
				executingActs.addElement(act);
				System.out.println("This is a call to ROS to do " + act);
			}
		};
		
		for (Variable var1 : fluentSolver.getVariables("Activity")) {
			var1.setColor(Color.GREEN);
		}
		for (Variable var1 : fluentSolver.getVariables("Task")) {
			var1.setColor(Color.BLUE);
		}
		
		animator.addDispatchingFunctions(fluentSolver, df);
		
		Fluent future = animator.getFuture();
		future.setColor(Color.WHITE);
		
		while (true) {
			System.out.println("Executing activities (press <enter> to refresh list):");
			for (int i = 0; i < executingActs.size(); i++) System.out.println(i + ". " + executingActs.elementAt(i));
			System.out.println("--");
//			System.out.print("Please enter activity to finish: ");  
			String input = "";
			BufferedReader br = new BufferedReader(new InputStreamReader(System.in));  
			try { input = br.readLine(); }
			catch (IOException e) { e.printStackTrace(); }
			
			for (int i = 0; i < executingActs.size(); i++) {
				Fluent fl = executingActs.get(i);
				if (fl.getTemporalVariable().getEET() > future.getTemporalVariable().getEST()) { 
					df.finish(fl);
					executingActs.remove(i);
				}
			}
			
//			if (!input.trim().equals("")) {
//				try {
//					df.finish(executingActs.elementAt(Integer.parseInt(input)));
//					executingActs.remove(Integer.parseInt(input));
//				}
//				catch (ArrayIndexOutOfBoundsException e1) { /* Ignore unknown activity */ }
//			}
		}
	}
	
	public static boolean plan(HTNPlanner planner, FluentNetworkSolver fluentSolver) {
		((CompoundSymbolicVariableConstraintSolver) fluentSolver.getConstraintSolvers()[0]).propagateAllSub();
		
		long startTime = System.nanoTime();
		boolean result = planner.backtrack();
		System.out.println("Found a plan? " + result);
		long endTime = System.nanoTime();

		planner.draw();
		ConstraintNetwork.draw(fluentSolver.getConstraintNetwork());
//		ConstraintNetwork.draw(fluentSolver.getConstraintSolvers()[1].getConstraintNetwork());

//		System.out.println(planner.getDescription());
		System.out.println("Took "+((endTime - startTime) / 1000000) + " ms"); 
		System.out.println("Finished");
		return result;
	}


}
