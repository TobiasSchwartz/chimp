package pfd0Symbolic;

import java.util.List;
import java.util.Vector;

import org.metacsp.framework.Constraint;
import org.metacsp.framework.ConstraintNetwork;
import org.metacsp.framework.ConstraintSolver;
import org.metacsp.framework.Variable;
import org.metacsp.framework.meta.MetaConstraint;
import org.metacsp.framework.meta.MetaVariable;
import org.metacsp.time.Bounds;

import unify.CompoundSymbolicVariable;



public class MoveBaseMetaConstraint extends MetaConstraint {

	/**
	 * 
	 */
	private static final long serialVersionUID = 2789371087819357936L;
	private static final String MOVE_BASE_NAME = "!move_base";
	private static final String ROBOTAT_NAME = "RobotAt";
	private static final int FROM_AREA_INDEX = 4;
	private static final int TO_AREA_INDEX = 4;
	
	private MoveBaseDurationEstimator durationEstimator;


	public MoveBaseMetaConstraint(MoveBaseDurationEstimator durationEstimator) {
		super(null, null);
		this.durationEstimator = durationEstimator;
	}

	
	/** 
	 * @return All {@link MetaVariable}s with the marking UNPLANNED and which have no unplanned 
	 * predecessors.
	 */
	@Override
	public ConstraintNetwork[] getMetaVariables() {
		FluentNetworkSolver groundSolver = (FluentNetworkSolver)this.getGroundSolver();
		Vector<ConstraintNetwork> ret = new Vector<ConstraintNetwork>();
		// for every variable that has the marking UNPLANNED and that has no unplanned predecessors 
		// a ConstraintNetwork is built.
		// this becomes a task.
		for (Variable var : groundSolver.getVariables()) {
			if (((Fluent) var).getCompoundSymbolicVariable().getPredicateName().equals(MOVE_BASE_NAME)) {
				//			if (var.getMarking() != null && var.getMarking().equals(markings.UNPLANNED)) {
				if (! checkDuration(var, groundSolver)) {
					ConstraintNetwork nw = new ConstraintNetwork(null);
					nw.addVariable(var);
					ret.add(nw);
				}
			}
			//			}
		}
		logger.finest("MetaVariables: " + ret);
		return ret.toArray(new ConstraintNetwork[ret.size()]);
	
	}
	

	// Checks if a duration has been set to a variable
	private boolean checkDuration(Variable var, FluentNetworkSolver groundSolver) {
		List<FluentConstraint> durationCons = 
				groundSolver.getFluentConstraintsOfTypeFrom((Fluent) var, FluentConstraint.Type.MOVEDURATION);
		return !durationCons.isEmpty();
	}

	
	/**
	 * Get all values for a given {@link MetaVariable}.
	 * @param metaVariable The {@link MetaVariable} for which we seek meta values.
	 * @return All meta values for the given{@link MetaVariables}.
	 */
	@Override
	public ConstraintNetwork[] getMetaValues(MetaVariable metaVariable) {
		ConstraintNetwork problematicNetwork = metaVariable.getConstraintNetwork();
		Fluent taskFluent = (Fluent)problematicNetwork.getVariables()[0];
		
		logger.fine("getMetaValues for: " + taskFluent);
		
		return estimateDuration(taskFluent);
	}
	
	private ConstraintNetwork[] estimateDuration(Fluent taskFluent) {
		Bounds bounds = null;
		String fromArea = getFromArea(taskFluent);
		if (fromArea != null && fromArea.length() > 0) {
			String toArea = getToArea(taskFluent);
			if (toArea != null && toArea.length() > 0) {
				bounds = durationEstimator.estimateDuration(fromArea, toArea);
			} else {
				logger.severe("No unique toArea found!");
			}
		} else {
			logger.severe("No fromArea found!");
		}
		
		if (bounds != null) {
			FluentConstraint duration = new FluentConstraint(FluentConstraint.Type.MOVEDURATION, bounds);
			duration.setFrom(taskFluent);
			duration.setTo(taskFluent);
			ConstraintNetwork ret = new ConstraintNetwork(null);
			ret.addConstraint(duration);
			return new ConstraintNetwork[] {ret};
		} else {
			return new ConstraintNetwork[] {};
		}
	}
	
	private String getToArea(Fluent taskFluent) {
		String[] possibleToAreas = taskFluent.getCompoundSymbolicVariable().getSymbolsAt(TO_AREA_INDEX);
		if (possibleToAreas.length != 1) {
			throw new IllegalStateException("FromArea is not ground");
		} else {
			return possibleToAreas[0];
		}
	}
	
	private String getFromArea(Fluent taskFluent) {
		FluentNetworkSolver groundSolver = (FluentNetworkSolver)this.getGroundSolver();
		List<FluentConstraint> preCons = 
				groundSolver.getFluentConstraintsOfTypeTo(taskFluent, FluentConstraint.Type.PRE);
		for (FluentConstraint con : preCons) {
			CompoundSymbolicVariable from = ((Fluent) con.getFrom()).getCompoundSymbolicVariable();
			if (from.getPredicateName().equals(ROBOTAT_NAME)) {
				String[] possibleFromAreas = from.getSymbolsAt(FROM_AREA_INDEX);
				
				if (possibleFromAreas.length != 1) {
					throw new IllegalStateException("FromArea is not ground");
				} else {
					return possibleFromAreas[0];
				}
			}
		}
		throw new IllegalStateException("No RobotAt precondition found");
	}
	
	
	@Override
	public void markResolvedSub(MetaVariable metaVariable, ConstraintNetwork metaValue) {
		// nothing to do here
	}

	@Override
	public void draw(ConstraintNetwork network) {
	}

	@Override
	public ConstraintSolver getGroundSolver() {
		return this.metaCS.getConstraintSolvers()[0];
	}

	@Override
	public String toString() {
		return "MoveBaseMetaConstraint";
	}

	@Override
	public String getEdgeLabel() {
		return null;
	}

	@Override
	public Object clone() {
		return null;
	}

	@Override
	public boolean isEquivalent(Constraint c) {
		return false;
	}

}