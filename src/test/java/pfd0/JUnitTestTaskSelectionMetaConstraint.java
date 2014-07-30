package pfd0;

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.metacsp.framework.ConstraintNetwork;
import org.metacsp.framework.Variable;
import org.metacsp.framework.VariablePrototype;

import pfd0.TaskApplicationMetaConstraint.markings;

public class JUnitTestTaskSelectionMetaConstraint {
	
	private PFD0Planner planner;
	private FluentNetworkSolver fluentSolver;

	@Before
	public void setUp() throws Exception {
		planner = new PFD0Planner(0,  600,  0);
		fluentSolver = (FluentNetworkSolver)planner.getConstraintSolvers()[0];
	}

	@After
	public void tearDown() throws Exception {}

	@Test
	public void test() {
		TaskSelectionMetaConstraint taskConstraint = new TaskSelectionMetaConstraint();
		TaskApplicationMetaConstraint pfd0Constraint = new TaskApplicationMetaConstraint();
		addMethods(pfd0Constraint, taskConstraint, fluentSolver);
		addOperators(pfd0Constraint, taskConstraint);	
		planner.addMetaConstraint(taskConstraint);
		
		Fluent getmugFluent = (Fluent) fluentSolver.createVariable("Robot1");
		getmugFluent.setName("get_mug(mug1)");
		getmugFluent.setMarking(markings.UNPLANNED);
		
		Fluent driveFluent = (Fluent) fluentSolver.createVariable("Robot1");
		driveFluent.setName("!drive(counter1)");
		driveFluent.setMarking(markings.UNPLANNED);
		
		createState(fluentSolver);
		
		
//		Fluent getmugFluent2 = (Fluent) groundSolver.createVariable("Robot2");
//		getmugFluent2.setName("get_mug mug1");
//		getmugFluent2.setMarking(markings.UNPLANNED);
		
//		createState(fluentSolver);
		
		FluentNetworkSolver groundSolver = (FluentNetworkSolver)planner.getConstraintSolvers()[0];
		ConstraintNetwork.draw(groundSolver.getConstraintNetwork(), "Constraint Network");
		
		assertTrue("Backtracking should generate a plan.", planner.backtrack());
		Variable[] vars = fluentSolver.getVariables();
		ArrayList<String> results = new ArrayList<String>();
		for (int i = 0; i < vars.length; i++) {
			results.add(i, ((Fluent) vars[i]).getCompoundNameVariable().getName());
		}
		assertTrue(results.contains("get_mug(mug1)"));
		assertTrue(results.contains("!drive(counter1)"));
		System.out.println(results);
		
		
		for (int i = 0; i < results.size(); i++) {
			if (results.get(i).equals("get_mug(mug1)")) {
				assertTrue(vars[i].getMarking() == markings.SELECTED);
			}
			if (results.get(i).equals("!drive(counter1)")) {
				assertTrue(vars[i].getMarking() == markings.SELECTED);
			}
			if (results.get(i).equals("RobotAt(table1)") 
					&& vars[i].getComponent().equals("Pre")) {
				assertTrue(vars[i].getMarking() == markings.SELECTED);
			}
		}
		
		assertTrue(results.size() == 5);
	}
	
	public static void createState(FluentNetworkSolver groundSolver) {
		Fluent robotAt = (Fluent) groundSolver.createVariable("RobotAt");
		robotAt.setName("RobotAt(table1)");
		robotAt.setMarking(markings.OPEN);
		
		Fluent on = (Fluent) groundSolver.createVariable("On");
		on.setName("On(mug1 counter1)");
		on.setMarking(markings.OPEN);
	}
	
	public static void addMethods(TaskApplicationMetaConstraint pfdConstraint,
			TaskSelectionMetaConstraint taskConstraint,
			FluentNetworkSolver groundSolver) {
		VariablePrototype drive = new VariablePrototype(groundSolver, "Component", "!drive(counter1)");
		VariablePrototype grasp = new VariablePrototype(groundSolver, "Component", "!grasp(mug1)");
		FluentConstraint before = new FluentConstraint(FluentConstraint.Type.BEFORE);
		before.setFrom(drive);
		before.setTo(grasp);
		PFD0Method getMug1Method = new PFD0Method("get_mug", new String[] {"mug1"}, 
				null, 
				new VariablePrototype[] {drive, grasp}, 
				new FluentConstraint[] {before});
//		PFD0Method getMug1Method = new PFD0Method("get_mug mug1", null, new String[] {"!drive counter1", "grasp mug1"});
		pfdConstraint.addMethod(getMug1Method);
		taskConstraint.addMethod(getMug1Method);
		
//		PFD0Method graspMug1Method = new PFD0Method("grasp mug1", null, new String[] {}); //new String[] {"fail"});
//		metaConstraint.addMethod(graspMug1Method);
		
	}
	
	public static void addOperators(TaskApplicationMetaConstraint pfdConstraint,
			TaskSelectionMetaConstraint taskConstraint) {
		PFD0Precondition robotatPre = new PFD0Precondition("RobotAt", new String[] {"table1"}, null);
		PFD0Operator driveCounter1Op = new PFD0Operator("!drive", new String[] {"counter1"}, 
				new PFD0Precondition[]{robotatPre}, 
				new String[] {"RobotAt(table1)"}, 
				new String[] {"RobotAt(counter1)"});
		pfdConstraint.addOperator(driveCounter1Op);
		taskConstraint.addOperator(driveCounter1Op);
		
		PFD0Precondition onPre = new PFD0Precondition("On", new String[] {"mug1", "counter1"}, null);
		PFD0Operator graspOp = new PFD0Operator("!grasp", new String[] {"mug1"}, 
				new PFD0Precondition[] {onPre}, 
				new String[] {"On(mug1 counter1)"}, 
				new String[] {"Holding(mug1)"});
		pfdConstraint.addOperator(graspOp);
		taskConstraint.addOperator(graspOp);
	}

}