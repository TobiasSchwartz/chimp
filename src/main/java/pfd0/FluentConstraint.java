package pfd0;

import org.metacsp.framework.Constraint;
import org.metacsp.framework.Variable;
import org.metacsp.framework.multi.MultiBinaryConstraint;

import unify.CompoundNameMatchingConstraint;
import unify.CompoundNameVariable;

public class FluentConstraint extends MultiBinaryConstraint {

	/**
	 * 
	 */
	private static final long serialVersionUID = 137380711080409334L;

	public static enum Type {MATCHES, DC, PRE, OPENS, CLOSES, BEFORE};

	private Type type;

	public FluentConstraint(Type type) {
		this.type = type;
	}

	@Override
	protected Constraint[] createInternalConstraints(Variable f, Variable t) {
		if (!( f instanceof Fluent) || !(t instanceof Fluent)) return null;

		if (this.type.equals(Type.MATCHES)) {
			SimpleBooleanValueConstraint scon = 
					new SimpleBooleanValueConstraint(SimpleBooleanValueConstraint.Type.EQUALS);
			SimpleBooleanValueVariable bf = ((Fluent) f).getSimpleBooleanValueVariable();
			scon.setFrom(bf);
			SimpleBooleanValueVariable bt = ((Fluent) t).getSimpleBooleanValueVariable();
			scon.setTo(bt);

			CompoundNameMatchingConstraint ncon = 
					new CompoundNameMatchingConstraint(CompoundNameMatchingConstraint.Type.MATCHES);
			CompoundNameVariable nf = ((Fluent) f).getCompoundNameVariable();
			ncon.setFrom(nf);
			CompoundNameVariable nt = ((Fluent) t).getCompoundNameVariable();
			ncon.setTo(nt);

			return new Constraint[]{scon, ncon};
		} else if (this.type.equals(Type.DC)) {
			// TODO nothing to add here?
		} else if (this.type.equals(Type.PRE)) {
			// TODO nothing to add here?
		}

		return null;
	}

	@Override
	public Object clone() {
		return new FluentConstraint(this.type);
	}

	@Override
	public String getEdgeLabel() {
		return this.type.toString();
	}

	@Override
	public boolean isEquivalent(Constraint c) {
		// TODO Auto-generated method stub
		return false;
	}

	public Type getType() {
		return type;
	}




}