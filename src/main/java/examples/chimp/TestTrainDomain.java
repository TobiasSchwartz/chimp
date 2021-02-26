package examples.chimp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Vector;
import java.util.logging.Level;

import org.metacsp.framework.Constraint;
import org.metacsp.framework.ConstraintNetwork;
import org.metacsp.framework.ValueOrderingH;
import org.metacsp.framework.Variable;
import org.metacsp.framework.meta.MetaConstraint;
import org.metacsp.utility.logging.MetaCSPLogging;

import dwr.DWRNavigationMetaConstraint;
import externalPathPlanning.LookUpTableDurationEstimator;
import fluentSolver.Fluent;
import fluentSolver.FluentConstraint;
import fluentSolver.FluentNetworkSolver;
import htn.HTNMetaConstraint;
import htn.HTNPlanner;
import htn.PlanReportroryItem;
import htn.guessOrdering.GuessOrderingMetaConstraint;
import htn.guessOrdering.GuessOrderingValOH;
import htn.valOrderingHeuristics.DeepestFewestsubsNewestbindingsValOH;
import htn.valOrderingHeuristics.DeepestWeightNewestbindingsValOH;
import htn.valOrderingHeuristics.UnifyDeepestWeightNewestbindingsValOH;
import htn.valOrderingHeuristics.UnifyEarlisttasksValOH;
import htn.valOrderingHeuristics.UnifyFewestsubsEarliesttasksNewestbindingsValOH;
import hybridDomainParsing.ClassicHybridDomain;
import hybridDomainParsing.DomainParsingException;
import hybridDomainParsing.HybridDomain;
import hybridDomainParsing.ProblemParser;
import hybridDomainParsing.ProblemSpecificationParsingException;
import hybridDomainParsing.SWTBahnProblemParser;
import hybridDomainParsing.classic.antlr.ChimpClassicReader;
import planner.CHIMP;
import planner.CHIMPProblem;
import postprocessing.PlanExtractor;
import resourceFluent.FluentResourceUsageScheduler;
import resourceFluent.FluentScheduler;
import resourceFluent.ResourceUsageTemplate;
import unify.CompoundSymbolicVariableConstraintSolver;

public class TestTrainDomain {

    static final boolean LOGGING = true;
    static final boolean GUESS_ORDERING = false;
    static final boolean PRINT_PLAN = true;
    static final boolean DRAW = false;


    public static void main(String[] args) {

    	String problemFile = "domains/swtbahn/swtbahnminiexample.pdl";
        String domainFile = "domains/swtbahn/swtbahn_domain.ddl";

		ValueOrderingH valOH = new UnifyEarlisttasksValOH();
//		ValueOrderingH valOH = new UnifyFewestsubsEarliesttasksNewestbindingsValOH();
//		ValueOrderingH valOH = new UnifyFewestsubsNewestbindingsValOH();
//		ValueOrderingH valOH = new DeepestNewestbindingsValOH();
//		ValueOrderingH valOH = new DeepestWeightNewestbindingsValOH();
//		ValueOrderingH valOH = new DeepestFewestsubsNewestbindingsValOH();
//        ValueOrderingH valOH = new UnifyDeepestWeightNewestbindingsValOH();
        
        CHIMP.CHIMPBuilder builder;
        
        try {
            builder = new CHIMP.CHIMPBuilder(domainFile, problemFile)
                    .valHeuristic(valOH)
                    .htnUnification(true);
            if (GUESS_ORDERING) {
                builder.guessOrdering(true);
            }

        } catch (DomainParsingException e) {
            e.printStackTrace();
            return;
        }
        CHIMP chimp = builder.build();

//		MetaCSPLogging.setLevel(planner.getClass(), Level.FINEST);
		MetaCSPLogging.setLevel(HTNMetaConstraint.class, Level.FINEST);

		MetaCSPLogging.setLevel(Level.FINE);
        if (!LOGGING) {
            MetaCSPLogging.setLevel(Level.OFF);
        }

        System.out.println("Found plan? " + chimp.generatePlan());
        chimp.printStats(System.out);

        if (PRINT_PLAN) {
            Variable[] planVector = chimp.extractActions();
            int c = 0;
            for (Variable act : planVector) {
                if (act.getComponent() != null)
                    System.out.println(c++ + ".\t" + act);
            }

            chimp.printFullPlan();
            chimp.drawPlanHierarchy(100);
            chimp.drawHierarchyNetwork();
            chimp.drawSearchSpace();
        }

    }
    
	private static Set<String> extractSymbolicConstants(ClassicHybridDomain domain) {
		Set<String> constants = new HashSet<>();
		for (PlanReportroryItem pri : domain.getOperators()) {
			constants.addAll(pri.getSymbolicConstants());
		}
		for (PlanReportroryItem pri : domain.getMethods()) {
			constants.addAll(pri.getSymbolicConstants());
		}
		return constants;
	}
	
	
	// 
	// COPY FROM TestDWRDomain
	//
	
	public static double plan(String problemFileName, String domainFileName) {
		
		ProblemParser pp = new ProblemParser(problemFileName);
		
		HybridDomain domain;
		try {
			domain = new HybridDomain(domainFileName);
		} catch (DomainParsingException e) {
			e.printStackTrace();
			return 0;
		}
		int[] ingredients = new int[] {1, domain.getMaxArgs()};
		String[][] symbols = new String[2][];
		symbols[0] =  domain.getPredicateSymbols();
		symbols[1] = pp.getArgumentSymbols();
		Map<String, String[]> typesInstancesMap = pp.getTypesInstancesMap();
		
		HTNPlanner planner = new HTNPlanner(0,  600000,  0, symbols, ingredients);
		planner.setTypesInstancesMap(typesInstancesMap);
		
		try {
			initPlanner(planner, domain);
		} catch (DomainParsingException e) {
			System.out.println("Error while parsing domain: " + e.getMessage());
			e.printStackTrace();
			return 0;
		}
		
		FluentNetworkSolver fluentSolver = (FluentNetworkSolver)planner.getConstraintSolvers()[0];
		pp.createState(fluentSolver, domain);
		((CompoundSymbolicVariableConstraintSolver) fluentSolver.getConstraintSolvers()[0]).propagateAllSub();
		
		MetaCSPLogging.setLevel(Level.INFO);
		MetaCSPLogging.setLevel(planner.getClass(), Level.FINE);		
		if (! LOGGING) {
			MetaCSPLogging.setLevel(Level.OFF);
		}

		double planning_time = plan(planner, fluentSolver);
		
		Variable[] allFluents = fluentSolver.getVariables();
		ArrayList<Variable> plan = new ArrayList<Variable>();
		int opCount = 0;
		int mCount = 0;
		for (Variable var : allFluents) {
			String component = var.getComponent();
			if (component == null) {
				plan.add(var);
			}
			else if (component.equals("Activity")) {
				plan.add(var);
				opCount++;
			} else if (component.equals("Task")) {
				mCount++;
			}
			
//			if (var.getMarking() == markings.OPEN) {
//				System.out.println(var);
//			}
		}
		
		for (MetaConstraint mcon : planner.getMetaConstraints()) {
			if (mcon instanceof HTNMetaConstraint) {
				System.out.println("#getMetaVariables-Invocations: " + ((HTNMetaConstraint) mcon).getVarsCNT);
			}
		}
		System.out.println("#Ops: " + opCount);
		System.out.println("#Compound Tasks: " + mCount);
		System.out.println("#Fluents: " + fluentSolver.getVariables().length);
		System.out.println("FluentConstraints: " + fluentSolver.getConstraints().length);
		System.out.println("---------------------------------------");
		// print number of applied meta values per metaconstraint:
//		System.out.println("Tried MetaValues: ");
//		int sum = 0;
//		for (Entry<MetaConstraint, Integer> entry: planner.getValCounters().entrySet()) {
//			System.out.println(entry);
//			sum += entry.getValue();
//		}
//		System.out.println("Sum: " + sum);
		System.out.println("---------------------------------------");

		if (PRINT_PLAN) {
			Variable[] planVector = plan.toArray(new Variable[plan.size()]);
			Arrays.sort(planVector, new Comparator<Variable>() {
				@Override
				public int compare(Variable o1, Variable o2) {
					// TODO Auto-generated method stub
					Fluent f1 = (Fluent)o1;
					Fluent f2 = (Fluent)o2;
					return ((int)f1.getTemporalVariable().getEST()-(int)f2.getTemporalVariable().getEST());
				}
			});

			int c = 0;
			for (Variable act : planVector) {
				if (act.getComponent() != null)
					System.out.println(c++ +".\t" + act);	
			}

			extractPlan(fluentSolver);
		}
		
		////////////////
		return planning_time;
		
	}
	
	public static double plan(HTNPlanner planner, FluentNetworkSolver fluentSolver) {
		((CompoundSymbolicVariableConstraintSolver) fluentSolver.getConstraintSolvers()[0]).propagateAllSub();
		
		long startTime = System.nanoTime();
		boolean result = planner.backtrack();
		long endTime = System.nanoTime();
		System.out.println("Found a plan? " + result);
		
		ConstraintNetwork cn = new ConstraintNetwork(null);
		for (Constraint con : fluentSolver.getConstraintNetwork().getConstraints()) {
			if (con instanceof FluentConstraint) {
				FluentConstraint fc = (FluentConstraint) con;
				if (fc.getType() == FluentConstraint.Type.MATCHES) {
					fc.getFrom().setMarking(HTNMetaConstraint.markings.UNIFIED);
					cn.addConstraint(fc);
				} else if (fc.getType() == FluentConstraint.Type.DC) {
					cn.addConstraint(fc);
				}
			}
		}
		
		if (DRAW) {
			planner.draw();
			ConstraintNetwork.draw(cn);
			ConstraintNetwork.draw(fluentSolver.getConstraintNetwork());
			ConstraintNetwork.draw(fluentSolver.getConstraintSolvers()[1].getConstraintNetwork());
		}

//		System.out.println(planner.getDescription());
		System.out.println("Took "+((endTime - startTime) / 1000000) + " ms"); 
		System.out.println("Finished");
		
//		System.out.println("AGAIN");
//		startTime = System.nanoTime();
//		result = planner.backtrack();
//		System.out.println("Found a plan? " + result);
//		endTime = System.nanoTime();
//
//		System.out.println("Took "+((endTime - startTime) / 1000000) + " ms"); 
//		System.out.println("Finished");
		
		return (endTime - startTime) / 1000000;
	}
	
	public static void extractPlan(FluentNetworkSolver fluentSolver) {
		PlanExtractor planEx = new PlanExtractor(fluentSolver);
		planEx.printPlan();
	}
	
	
	public static void initPlanner(HTNPlanner planner, HybridDomain domain) throws DomainParsingException {
		// load domain
		domain.parseDomain(planner.getTypesInstancesMap());
		
		// init meta constraints based on domain
		ValueOrderingH valOH = new DeepestFewestsubsNewestbindingsValOH();
//		ValueOrderingH valOH = new DeepestNewestbindingsValOH(); // not working
//		ValueOrderingH valOH = new DeepestWeightNewestbindingsValOH();	
//		ValueOrderingH valOH = new ShallowFewestsubsNewestbindingsValOH();
//		ValueOrderingH valOH = new UnifyDeepestWeightNewestbindingsValOH();
//		ValueOrderingH valOH = new UnifyEarlisttasksValOH(); // not working
//		ValueOrderingH valOH = new UnifyFewestsubsEarliesttasksNewestbindingsValOH();
//		ValueOrderingH valOH = new UnifyFewestsubsNewestbindingsValOH();
//		ValueOrderingH valOH = new UnifyWeightNewestbindingsValOH();
//		ValueOrderingH valOH = new DeepestWeightOldestbindingsValOH();	
		
		HTNMetaConstraint htnConstraint = new HTNMetaConstraint(valOH);
		htnConstraint.addOperators(domain.getOperators());
		htnConstraint.addMethods(domain.getMethods());
		Vector<ResourceUsageTemplate> fluentResourceUsages = domain.getFluentResourceUsages();
		htnConstraint.setResourceUsages(fluentResourceUsages);
		
		
		for (FluentScheduler fs : domain.getFluentSchedulers()) {
			planner.addMetaConstraint(fs);
		}
		
		for (FluentResourceUsageScheduler rs : domain.getResourceSchedulers()) {
			planner.addMetaConstraint(rs);
		}
		
		if (GUESS_ORDERING) {
			ValueOrderingH guessOH = new GuessOrderingValOH();
			GuessOrderingMetaConstraint ordConstraint = new GuessOrderingMetaConstraint(guessOH);
			planner.addMetaConstraint(ordConstraint);
		}
		
		planner.addMetaConstraint(htnConstraint);
	}

}
