package hybridDomainParsing;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.Vector;
import java.util.logging.Level;

import org.metacsp.framework.Constraint;
import org.metacsp.framework.Variable;
import org.metacsp.multi.allenInterval.AllenIntervalConstraint;
import org.metacsp.time.Bounds;
import org.metacsp.utility.logging.MetaCSPLogging;

import fluentSolver.Fluent;
import fluentSolver.FluentConstraint;
import fluentSolver.FluentNetworkSolver;
import htn.HTNMetaConstraint;
import planner.CHIMPProblem;
import resourceFluent.ResourceUsageTemplate;
import unify.CompoundSymbolicVariable;


/**
 * A custom parser for the SWTBahn specification language. 
 * Can optionally also generate a problem file that can be used as input for the normal HTN planner.
 * Expects an UTF8 encoding.
 * 
 * @author Tobias Schwartz
 *
 */
public class SWTBahnProblemParser implements CHIMPProblem {
	
	public static final String PROBLEM_KEYWORD = "Problem";
	public static final String FLUENT_KEYWORD = "Fluent";
	public static final String TASK_KEYWORD = "Task";
	private static final String ARGUMENT_SYMBOLS_KEYWORD = "ArgumentSymbols";
	private static final String INSTANCES_KEYWORD = "Instances";
	private static final String CONSTRAINT_KEYWORD = "Constraint";
	
	private static final String BAHN_KEYWORD = "module";
	private static final String BLOCK_KEYWORD = "blocks";
	private static final String POINT_KEYWORD = "points";
	private static final String CROSSING_KEYWORD = "crossings";
	private static final String PLATFORM_KEYWORD = "platforms";
	private static final String SIGNAL_KEYWORD = "signals";
	private static final String LAYOUT_KEYWORD = "layout";
	private static final String TRAIN_KEYWORD = "trains";
	private static final String GOAL_KEYWORD = "goals";
	
	private static final String FLUENT_CONNECTED_PREFIX = "c";
	private static final String FLUENT_SIGNAL_PREFIX = "s";
	private static final String FLUENT_TRAIN_PREFIX = "t";
	private static final String FLUENT_GOAL_PREFIX = "g";
	
	
	
	private static final String N = "n";
	
	private final Map<String, String> fluentElementsMap = new HashMap<String, String>();
	private final Map<String, String> taskElementsMap = new HashMap<String, String>();
	private String[] problemStrs;
	private Set<String> argumentSymbols = new HashSet<>();
	private Map<String, String[]> typesInstancesMap;
	
	private int fluentConnectedCounter = 0;
	private int fluentSignalCounter = 0;
	private int fluentTrainCounter = 1;
	private int taskCounter = 1;
	
	
	public static void main(String[] args) {
		MetaCSPLogging.setLevel(Level.FINE);
		System.out.println("Parsing test of a SWTBahn config file...");
		
		String filename = "domains/swtbahn/test.bahn";
		
		
		
		try {
			SWTBahnProblemParser parser = new SWTBahnProblemParser(filename, true);
			
		} catch (ProblemSpecificationParsingException e) {
			e.printStackTrace();
		}
		
	}
	
	public SWTBahnProblemParser(String fileName) throws ProblemSpecificationParsingException {
		new SWTBahnProblemParser(fileName, false);
	}
	
	
	
	public SWTBahnProblemParser(String fileName, boolean writeToPdlFile) throws ProblemSpecificationParsingException {
		String problemSpecification = readSpecificationFile(fileName);
		String problemName = parseProblemFile(problemSpecification);
		
		if (writeToPdlFile) {
			String outputPath = new File(fileName).getParent();
			outputPath += "\\" + problemName.toLowerCase();
			writeProblemfile(outputPath);
		}
	}
	
	private void reset() {
		fluentElementsMap.clear();
		taskElementsMap.clear();
	}
	
	private String parseProblemFile(String problemFile) throws ProblemSpecificationParsingException {
		reset();
		
		problemStrs = parseKeyword(BAHN_KEYWORD, problemFile);
		if (problemStrs == null || problemStrs.length == 0) {
			throw new ProblemSpecificationParsingException("The specification file has the wrong format or is empty.");
		}
		String name = problemStrs[0].trim().split("\\s+")[0];
		
		System.out.println("Successfully read in " + name + ".");
		for (String problemStr : problemStrs) {
			parseProblem(problemStr);
		}
		
		return name;
	}	

	private static String readSpecificationFile(String fileName) throws ProblemSpecificationParsingException {
		String problemSpecification = null;
		try (BufferedReader br = new BufferedReader(new FileReader(fileName, StandardCharsets.UTF_8))) {
				StringBuilder sb = new StringBuilder();
				String line = br.readLine();
				while (line != null) {
					if (!line.trim().startsWith("#")) {
						sb.append(line);
						sb.append('\n');
					}
					line = br.readLine();
				}
				problemSpecification = sb.toString();
		} catch (IOException e) { 
			throw new ProblemSpecificationParsingException(e.getMessage());
		}
		if (problemSpecification == null) {
			throw new ProblemSpecificationParsingException("Could not read the SWTBahn specification file " + fileName);
		}
		return problemSpecification;
	}

	
	private void parseProblem(String problem) throws ProblemSpecificationParsingException {
		parseTypes(problem);
		parseConfiguration(problem);
		parseGoals(problem);
		
		printTypeMap();
		printFluentMap();
		
	}

	/**
	 * Parses the layout section of the SWTBahn specification file.
	 * Creates all static fluents for connections and signal placement 
	 * 
	 * @param problem
	 * @throws ProblemSpecificationParsingException
	 */
	private void parseConfiguration(String problem) throws ProblemSpecificationParsingException {
		
		for (String typeDef : parseKeyword(LAYOUT_KEYWORD, problem)) {
			String[] lines = typeDef.split("\n");
			for (String line : lines) {
				String[] config = line.trim().split("\\s+");
				if (config.length != 3) {
					continue;
				}
				//TODO: Check that all elements are actually defined
				String l1 = config[0].trim();
				String op = config[1].trim();
				String l2 = config[2].trim();
				
				if (!(isValidTypeInstance(l1) && isValidTypeInstance(l2))) {
					MetaCSPLogging.getLogger(SWTBahnProblemParser.class).warning(
							"Warning: Some instances are not defined in layout definition '" + line.trim() + "'. Skipped.");
					continue;
				}
				
				if (isSignal(l1) && "--".equals(op)) {
					String fluentKey = FLUENT_SIGNAL_PREFIX + fluentSignalCounter;
					String fluent = "SignalAt(" + l1 + " " + l2 + ")";
					fluentElementsMap.put(fluentKey, fluent);
					fluentSignalCounter++;
					continue;
				}
				
				if (isTrain(l1) && "--".equals(op)) {
					String fluentKey = FLUENT_TRAIN_PREFIX + fluentTrainCounter;
					String fluent = "TrainAt(" + l1 + " " + l2 + ")";
					fluentElementsMap.put(fluentKey, fluent);
					fluentTrainCounter++;
					continue;
				}
				
				if ("--".equals(op) || "->".equals(op)) {
					String fluentKey = FLUENT_CONNECTED_PREFIX + fluentConnectedCounter;
					String fluent = "Connected(" + l1 + " " + l2 + ")";
					fluentElementsMap.put(fluentKey, fluent);
					fluentConnectedCounter++;
				}
				if ("--".equals(op) || "<-".equals(op)) {
					String fluentKey = FLUENT_CONNECTED_PREFIX + fluentConnectedCounter;
					String fluent = "Connected(" + l2 + " " + l1 + ")";
					fluentElementsMap.put(fluentKey, fluent);
					fluentConnectedCounter++;
				}
			}
		}
	}



	private boolean isValidTypeInstance(String typeInstance) {
		for(String[] typeInstances : typesInstancesMap.values()) {
			if (typeInstances != null && Arrays.asList(typeInstances).contains(typeInstance)) {
				return true;
			}
		}
		return false;
	}



	/**
	 * Small helper function to determine whether a given element is of any of the available signal types.
	 * 
	 * @param signalCandidate
	 * @return true if the input is a subtype of signal, false otherwise. 
	 */
	private boolean isSignal(String signalCandidate) {
		String[] signalTypesArr = typesInstancesMap.get(SIGNAL_KEYWORD);
		if (signalTypesArr == null || signalTypesArr.length == 0) {
			return false;
		}
		List<String> signalTypes = Arrays.asList(signalTypesArr);
		for (String signalType : signalTypes) {
			List<String> signals = Arrays.asList(typesInstancesMap.get(signalType));
			if (signals.contains(signalCandidate)) {
				return true;
			}
		}
		return false;
	}
	
	private boolean isTrain(String potentialTrain) {
		String[] trainInstancesArr = typesInstancesMap.get(TRAIN_KEYWORD);
		if (trainInstancesArr == null || trainInstancesArr.length == 0) {
			return false;
		}
		List<String> trainInstances = Arrays.asList(trainInstancesArr);
		return trainInstances.contains(potentialTrain);
	}

	private void parseTypes(String problem) {
		typesInstancesMap = new HashMap<String, String[]>();
		
		String[] blockTypes = parseType(BLOCK_KEYWORD, problem, new String[] {"up", "down"});
		typesInstancesMap.put(BLOCK_KEYWORD, blockTypes);
		
		String[] platformTypes = parseType(PLATFORM_KEYWORD, problem, new String[] {"up", "down"});
		typesInstancesMap.put(PLATFORM_KEYWORD, platformTypes);
		
		String[] pointTypes = parseType(POINT_KEYWORD, problem, new String[] {"stem", "side", "straight"});
		typesInstancesMap.put(POINT_KEYWORD, pointTypes);
		
		String[] crossingTypes = parseType(CROSSING_KEYWORD, problem, new String[] {"up1", "down1", "up2", "down2"});
		typesInstancesMap.put(CROSSING_KEYWORD, crossingTypes);
		
		String[] trainTypes = parseType(TRAIN_KEYWORD, problem);
		typesInstancesMap.put(TRAIN_KEYWORD, trainTypes);
		
		parseSignals(problem);	
		
		
	}
	
	private void parseSignals(String problem) {
		for (String typeDef : parseKeyword(SIGNAL_KEYWORD, problem)) {
			String[] types = typeDef.split("\\s+");
			for (int i = 0; i < types.length; i++) {
				if (i%2 == 0) {
					// complicated way of using a set to add new signal (types)
					String[] curr = typesInstancesMap.get(SIGNAL_KEYWORD);
					if (curr == null) {
						curr = new String[] { types[i] };
						typesInstancesMap.put(SIGNAL_KEYWORD, curr);
					}
					Set<String> cs = new HashSet<>();
					for (String c : curr) {
						cs.add(c);
					}
					cs.add(types[i]);
					typesInstancesMap.put(SIGNAL_KEYWORD, cs.toArray(new String[0]));
					
				} else {
					String[] curr = typesInstancesMap.get(types[i-1]);
					if (curr == null) {
						curr = new String[] { types[i] };
						typesInstancesMap.put(types[i-1], curr);
					}
					Set<String> cs = new HashSet<>();
					for (String c : curr) {
						cs.add(c);
					}
					cs.add(types[i]);
					typesInstancesMap.put(types[i-1], cs.toArray(new String[0]));
				}
			}
		}
	}
	private String[] parseType(String keyword, String problem) {
		return parseType(keyword, problem, null);
	}
	
	private String[] parseType(String keyword, String problem, String[] variations) {
		String[] typeInstances = null;

		for (String typeDef : parseKeyword(keyword, problem)) {
			String[] types = typeDef.split("\\s+");
			if (variations == null || variations.length == 0) {
				return types;
			}
			
			int var = variations.length;
			int finalLength = types.length * var;
			typeInstances = new String[finalLength];
			
			for (int i = 0; i < types.length; i++) {
				for (int j = 0; j < var; j++) {
					typeInstances[(i*var)+j] = types[i] + "." + variations[j];
				}
			}
			
			addInternalConnections(keyword, typeInstances, variations);
		}
		return typeInstances;
	}
	
	
	
	
	private void addInternalConnections(String type, String[] instances, String[] endpoints) {
		int l = endpoints.length;
		
		if (endpoints == null || l == 0) {
			MetaCSPLogging.getLogger(SWTBahnProblemParser.class).info("No endpoints available, no internal connections were created.");
			return;
		}
		
		int numInstances = instances.length / l;
		
		for (int x = 0; x < numInstances; x++) {
			for (int i = 0; i < l; i++) {
				for (int j = 0; j < l; j++) {
					if (i == j)
						continue;

					String from = instances[x * l + i];
					String to = instances[x * l + j];

					if ((from.endsWith("straight") && to.endsWith("side")) ||
						(from.endsWith("side") && to.endsWith("straight"))) {
						continue;
					}

					addConnectedFluent(from, to);
				}
			}
		}

	}

	private void addConnectedFluent(String from, String to) {
		String fluentKey = FLUENT_CONNECTED_PREFIX + fluentConnectedCounter;
		String fluent = "Connected(" + from + " " + to + ")";
		fluentElementsMap.put(fluentKey, fluent);
		MetaCSPLogging.getLogger(SWTBahnProblemParser.class).fine("Info: Added new internal connection: " + from + " -> " + to);
		fluentConnectedCounter++;
	}
	
	

	private void parseGoals(String problem) {
		for (String typeDef : parseKeyword(GOAL_KEYWORD, problem)) {
			String[] lines = typeDef.split("\n");
			for (String line : lines) {
				String[] config = line.trim().split("\\s+");
				if (config.length != 3) {
					MetaCSPLogging.getLogger(SWTBahnProblemParser.class).warning(
							"Warning: Unsupported goal specification '" + line.trim() + "'. Skipped.\n"
									+ "Supported format: '{train} -- {destination}'");
					continue;
				}
				String l1 = config[0].trim();
				String op = config[1].trim();
				String l2 = config[2].trim();
				
				if (!(isValidTypeInstance(l1) && isValidTypeInstance(l2))) {
					MetaCSPLogging.getLogger(SWTBahnProblemParser.class).warning(
							"Warning: Some instances are not defined in goal specification '" + line.trim() + "'. Skipped.");
					continue;
				}
				
				if (isTrain(l1) && "--".equals(op) && !isTrain(l2)) {
					createDriveTask(l1, l2);
				} else {
					MetaCSPLogging.getLogger(SWTBahnProblemParser.class).warning(
							"Warning: Unsupported goal specification '" + line.trim() + "'. Skipped.\n"
									+ "Only driving tasks are currently supported.");
				}
				
			}
		}
	}
	
	

	/**
	 * Creates a new task in the format of
	 * (Task t1 drive(train1 signal2))
	 * 
	 * where t1 is the key
	 * and "drive(train1 signal2)" is the value
	 * added to the task map.
	 * 
	 * @param train
	 * @param destination
	 */
	private void createDriveTask(String train, String destination) {
		String taskKey = FLUENT_GOAL_PREFIX + taskCounter;
		String task = "drive(" + train + " " + destination + ")";
		taskElementsMap.put(taskKey, task);
		MetaCSPLogging.getLogger(SWTBahnProblemParser.class).fine("Info: Added new task " + taskKey + ": " + task);
		taskCounter++;
	}

	@Override
	public void createState(FluentNetworkSolver fluentSolver, ClassicHybridDomain domain) {
		Map<String, Variable> varsMap = new HashMap<String, Variable>(fluentElementsMap.size() 
				+ taskElementsMap.size());
		
		// create fluents
		for (Map.Entry<String, String> e : fluentElementsMap.entrySet()) {
			Fluent var = (Fluent) fluentSolver.createVariable();
			int firstClosing = e.getValue().indexOf(')') + 1;
			String predicate = e.getValue();
			String symbolicPart = predicate;
			if (firstClosing != e.getValue().length()) {
				String intPart = predicate.substring(predicate.lastIndexOf('(') + 1 , predicate.length() - 1);
				String[] intElements = intPart.split(" ");
				for (int i = 0; i < intElements.length; i++) {
					var.getIntegerVariables()[i].setConstantValue(Integer.valueOf(intElements[i]));
				}
				symbolicPart = symbolicPart.substring(0, firstClosing);
	
			}
			var.setName(symbolicPart);
			var.setMarking(HTNMetaConstraint.markings.OPEN);
			varsMap.put(e.getKey(), var);
		}
	
		Set<String> operatorNames = domain.getOperatorNames();
		// create tasks
		for (Map.Entry<String, String> e : taskElementsMap.entrySet()) {
			String fullName = e.getValue();
			String predicateName = fullName.split("\\(")[0];
			String component;
			if (operatorNames.contains(predicateName)) {
				component = Fluent.ACTIVITY_TYPE_STR;
			} else {
				component = Fluent.TASK_TYPE_STR;
			}
			Fluent var = (Fluent) fluentSolver.createVariable(component);
			var.setName(fullName);
			var.setMarking(HTNMetaConstraint.markings.UNPLANNED);
			varsMap.put(e.getKey(), var);
		}
		
		// create AllenIntervals
		for (String stateStr : problemStrs) {
			fluentSolver.addConstraints(createAllenIntervalConstraints(stateStr, varsMap));
		}
		
		// create Ordering Constraints
		for (String stateStr : problemStrs) {
			fluentSolver.addConstraints(createOrderingConstraints(stateStr, varsMap));
		}
	
		// create FluentResourceUsage constraints
		fluentSolver.addConstraints(createResourceUsageConstraints(domain.getFluentResourceUsages(), varsMap.values()));
	
	}
	
	private Constraint[] createResourceUsageConstraints(
			List<ResourceUsageTemplate> fluentResourceUsages,
			Collection<Variable> vars) {
		List<Constraint> ret = new ArrayList<Constraint>();
		Map<String, List<ResourceUsageTemplate>> usageTemplatesMap = HTNMetaConstraint.createResourceUsagesMap(fluentResourceUsages);
		
		for(Variable var : vars) {
			CompoundSymbolicVariable csv = ((Fluent) var).getCompoundSymbolicVariable();
			String symbol = csv.getPredicateName();
			
			List<ResourceUsageTemplate> rtList = usageTemplatesMap.get(symbol);
			if (rtList != null) {
				for (ResourceUsageTemplate rt : rtList) {
					FluentConstraint resourceCon = 
							new FluentConstraint(FluentConstraint.Type.RESOURCEUSAGE, rt);
					resourceCon.setFrom(var);
					resourceCon.setTo(var);
					ret.add(resourceCon);
				}
			}
		}
		
		return ret.toArray(new Constraint[ret.size()]);
	}
	
	private AllenIntervalConstraint[] createAllenIntervalConstraints(String stateStr,
			Map<String, Variable> fluentsVarsMap) {
		// Parse AllenIntervalConstraints:
		String[] constraintElements = HybridDomain.parseKeyword(HybridDomain.CONSTRAINT_KEYWORD, stateStr);
		AllenIntervalConstraint[] ret = new AllenIntervalConstraint[constraintElements.length];
		for (int i = 0; i < constraintElements.length; i++) {
			String conElement = constraintElements[i];
			String constraintName = null;
			Vector<Bounds> bounds = null;
			if (conElement.contains("[")) {
				constraintName = conElement.substring(0,conElement.indexOf("[")).trim();
				String boundsString = conElement.substring(conElement.indexOf("["),conElement.lastIndexOf("]")+1);
				String[] splitBounds = boundsString.split("\\[");
				bounds = new Vector<Bounds>();
				for (String oneBound : splitBounds) {
					if (!oneBound.trim().equals("")) {
						String lbString = oneBound.substring(oneBound.indexOf("[")+1,oneBound.indexOf(",")).trim();
						String ubString = oneBound.substring(oneBound.indexOf(",")+1,oneBound.indexOf("]")).trim();
						long lb, ub;
						if (lbString.equals("INF")) lb = org.metacsp.time.APSPSolver.INF;
						else lb = Long.parseLong(lbString);
						if (ubString.equals("INF")) ub = org.metacsp.time.APSPSolver.INF;
						else ub = Long.parseLong(ubString);
						bounds.add(new Bounds(lb,ub));
					}
				}
			}
			else {
				constraintName = conElement.substring(0,conElement.indexOf("(")).trim();
			}
			String from = null;
			String to = null;
			String fromSeg = null;
			if (constraintName.equals("Duration") || constraintName.equals("Release") 
					|| constraintName.equals("Deadline")) {
				from = conElement.substring(conElement.indexOf("(")+1, conElement.indexOf(")")).trim();
				to = from;
			}
			else {
				fromSeg = conElement.substring(conElement.indexOf("("));
				from = fromSeg.substring(fromSeg.indexOf("(")+1, fromSeg.indexOf(",")).trim();
				to = fromSeg.substring(fromSeg.indexOf(",")+1, fromSeg.indexOf(")")).trim();
			}
	
			AllenIntervalConstraint con = null;
			if (bounds != null) {
				con = new AllenIntervalConstraint(AllenIntervalConstraint.Type.valueOf(constraintName),bounds.toArray(new Bounds[bounds.size()]));
			}
			else con = new AllenIntervalConstraint(AllenIntervalConstraint.Type.valueOf(constraintName));
			
			con.setFrom(fluentsVarsMap.get(from));
			con.setTo(fluentsVarsMap.get(to));
			ret[i] = con;			
		}
		return ret;
	}
	
	private Constraint[] createOrderingConstraints(String stateStr,
			Map<String, Variable> fluentsVarsMap) {
		// Parse AllenIntervalConstraints:
		String[] constraintElements = HybridDomain.parseKeyword(HybridDomain.ORDERING_CONSTRAINT_KEYWORD, stateStr);
		Constraint[] ret = new Constraint[constraintElements.length];
		for (int i = 0; i < constraintElements.length; i++) {
			String orderingElement = constraintElements[i];
			String fromKey = orderingElement.substring(0,orderingElement.indexOf(" ")).trim();
			String toKey = orderingElement.substring(orderingElement.indexOf(" ")).trim();
			FluentConstraint con = new FluentConstraint(FluentConstraint.Type.BEFORE);
			
			con.setFrom(fluentsVarsMap.get(fromKey));
			con.setTo(fluentsVarsMap.get(toKey));
			ret[i] = con;			
		}
		return ret;
	}
	
	@Override
	public String[] getArgumentSymbols() {
		return argumentSymbols.toArray(new String[argumentSymbols.size()]);
	}
	
	@Override
	public void addArgumentSymbols(Collection<String> symbols) {
		argumentSymbols.addAll(symbols);
	}
	
	@Override
	public Map<String, String[]> getTypesInstancesMap() {
		return typesInstancesMap;
	}
	
	private String[] parseKeyword(String keyword, String everything) {
		Vector<String> elements = new Vector<String>();
		int lastElement = everything.lastIndexOf(keyword);

		while (lastElement != -1) {
//			System.out.print("Found keyword '" + keyword + "' at position " + lastElement);
			int bw = lastElement;
			int fw = lastElement;
			
			while (bw > 0 && everything.charAt(bw) != '\n') {
				bw--;
			}
			
			int indentNumn = fw - bw;
//			System.out.println(" with indent of " + indentNumn);
			
			String indent = everything.substring(bw, fw);
			String matchingEnd = indent + "end";
			if (!indent.startsWith("\n")) {
				matchingEnd = "\n" + matchingEnd; 
			}
			
			fw = everything.indexOf(matchingEnd, (fw + keyword.length()));
			
			if (fw != -1) {
//				System.out.println("Found matching 'end' at position " + fw);
				String element = everything.substring(lastElement+keyword.length(),fw).trim();
				if (!element.startsWith(",") && !element.trim().equals("")) elements.add(element);
			}
			
			everything = everything.substring(0,bw);
			lastElement = everything.lastIndexOf(keyword);
		}
		return elements.toArray(new String[elements.size()]);		
	}
	
	private void writeProblemfile(String filename) {
		String indent = "\t";
		
		File outputFile = preprocessOutputFile(filename);
		if (outputFile == null) return;
		
		System.out.println("Writing problem file into " + outputFile);
		
		try(BufferedWriter out = new BufferedWriter(new FileWriter(outputFile, StandardCharsets.UTF_8))) {
			out.append("(" + PROBLEM_KEYWORD);
			out.newLine();
			out.newLine();
			
			// ARGUMENT SYMBOLS
			
			out.append("(" + ARGUMENT_SYMBOLS_KEYWORD);
			out.newLine();
			for (String[] typeInstances : typesInstancesMap.values()) {
				if (typeInstances != null && typeInstances.length != 0) {
					out.append(indent);
					for (String typeInstance : typeInstances) {
						out.append(typeInstance);
						out.append(" ");
					}
					out.newLine();
				}
			}
			out.append(indent);
			for (String type : typesInstancesMap.keySet()) {
				out.append(type);
				out.append(" ");
			}
			out.newLine();
			out.append(")");
			out.newLine();
			out.newLine();
			
			// INSTANCES
			
			for (Map.Entry<String, String[]> typeInstances : typesInstancesMap.entrySet()) {
				if (typeInstances != null && typeInstances.getValue() != null) {
					out.append("(");
					out.append(INSTANCES_KEYWORD);
					out.append(" ");
					out.append(typeInstances.getKey());

					for (String typeInstance : typeInstances.getValue()) {
						out.append(" ");
						out.append(typeInstance);
					}
					
					out.append(")");
					out.newLine();
				}
			}
			
			
			// FLUENTS
			
			List<Map.Entry<String, String>> fluentElements = new LinkedList<>(fluentElementsMap.entrySet());
			fluentElements.sort(Comparator.comparing(Map.Entry::getKey));
			
			for (Map.Entry<String, String> fluentInstances : fluentElements) {
				out.newLine();

				out.append("(");
				out.append(FLUENT_KEYWORD);
				out.append(" ");
				out.append(fluentInstances.getKey());
				out.append(" ");
				out.append(fluentInstances.getValue());
				out.append(")");
				out.newLine();
				
				out.append("(");
				out.append(CONSTRAINT_KEYWORD);
				out.append(" Release[0,0](");
				out.append(fluentInstances.getKey());
				out.append("))");
				out.newLine();
			}
			
			out.newLine();
			
			// TASKS
			
			for (Map.Entry<String, String> taskInstances : taskElementsMap.entrySet()) {
				out.append("(");
				out.append(TASK_KEYWORD);
				out.append(" ");
				out.append(taskInstances.getKey());
				out.append(" ");
				out.append(taskInstances.getValue());
				out.append(")");
				out.newLine();
			}
			
			out.newLine();
			
			out.append(")");
			
			out.flush();
			
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}



	private File preprocessOutputFile(String filename) {
		filename = filename.trim();
		if (!filename.endsWith(".pdl")) {
			filename += ".pdl";
		}
		File outputFile = new File(filename);
		
		System.out.println("Trying to write specification to " + outputFile);
		
		if (outputFile.isFile()) {
			System.err.println("The file already exisits. Do you want to override it?");
			Scanner scanner = new Scanner(System.in);
			String answer = scanner.next();
			if ("y".equals(answer) || "yes".equals(answer) || "j".equals(answer) || "ja".equals(answer)) {
				scanner.close();
				System.out.println("\nWriting output to " + filename);
			} else {
				scanner.close();
				System.out.println("\nGood Bye.");
				return null;
			}
		}
		return outputFile;
	}
	
	private void printTypeMap() {
		for(Map.Entry<String, String[]> e : typesInstancesMap.entrySet()) {
			if (e == null || e.getValue() == null) {
				continue;
			}
			System.out.println(e.getKey().toUpperCase());
			System.out.print("  > ");
			for (String type : e.getValue()) {
				System.out.print(type + " ");
			}
			System.out.println();
		}
	}
	
	private void printFluentMap() {
		for(Map.Entry<String, String> e : fluentElementsMap.entrySet()) {
			System.out.print(e.getKey());
			System.out.print(": ");
			System.out.println(e.getValue());
		}
	}

}
