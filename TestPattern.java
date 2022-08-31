package TgfdDiscovery;

import Infra.*;
import VF2Runner.VF2SubgraphIsomorphism;
import graphLoader.DBPediaLoader;
import graphLoader.GraphLoader;
import org.jetbrains.annotations.NotNull;
import org.jgrapht.Graph;
import org.jgrapht.GraphMapping;
import org.jgrapht.alg.isomorphism.VF2AbstractIsomorphismInspector;

import java.io.*;
import java.time.Duration;
import java.time.Period;
import java.util.*;
import java.util.Map.Entry;
import java.util.stream.Collectors;
public class TestPattern {
    //TODO: basic arguments: introduce by steps, construct
    public int NUM_OF_VERTICES_IN_ALL_GRAPH;
    public int NUM_OF_EDGES_IN_ALL_GRAPH;
    private HashMap<String, Integer> vertexHistogram = new HashMap<>();
    private List<Entry<String, Integer>> sortedVertexHistogram;
    private List<Entry<String, Integer>> sortedEdgeHistogram;
    private int gamma = 20;
    private int frequentSetSize = Integer.MAX_VALUE;
    private HashSet<String> activeAttributesSet;
    private final ArrayList<Double> vertexFrequenciesList = new ArrayList<>();
    private final ArrayList<Double> edgeFrequenciesList = new ArrayList<>();
    public Map<String, HashSet<String>> vertexTypesToAttributesMap;
    public PatternTree patternTree;
    private int previousLevelNodeIndex = 0;
    private int candidateEdgeIndex = 0;
    private int currentVSpawnLevel = 0;
    private boolean reUseMatches = true;
    private boolean interestingTGFDs = false;
    private double theta = 0.5;
    private int k = 5;
    private boolean noSupportPruning = false;
    private boolean skipK1 = true;
    public boolean noMinimalityPruning = false;
    private ArrayList<ArrayList<TGFD>> tgfds = new ArrayList<>();
    private int numOfSnapshots = 1;
    private ArrayList<Double> patternSupportsList = new ArrayList<>();
    private ArrayList<Double> constantTgfdSupportsList = new ArrayList<>();
    private ArrayList<Double> generalTgfdSupportsList = new ArrayList<>();
    private boolean useChangeFile = false;
    private ArrayList<Set<String>> vertexOnMachine = new ArrayList<>();


    public TestPattern(){

    }
    //TODO: load and histogram
    public GraphLoader loadGraph(){
        String prefix = "/home/ubuntu/";
        DBPediaLoader dbpedia2015 = new DBPediaLoader(new ArrayList<>(), new ArrayList<>(Collections.singletonList(prefix+"2015/2015types.ttl")), new ArrayList<>(Arrays.asList(prefix+"2015/2015literals.ttl", prefix+"2015/2015objects.ttl")));
        for (int vSpawnLevel = 0; vSpawnLevel <= this.getK(); vSpawnLevel++) {
            getTgfds().add(new ArrayList<>());
        }
        return dbpedia2015;
    }

    public void loadPartition(){
        for(int i = 0;i < 4;i++){
            vertexOnMachine.add(new HashSet<>());
            try {
                File myObj = new File("/home/ubuntu/machine-"+i+".txt");
                Scanner myReader = new Scanner(myObj);
                String data = "";
                while (myReader.hasNextLine()) {
                    data = myReader.nextLine();
                }
                String[] tmp = data.trim().split("\\s+");
                vertexOnMachine.get(i).addAll(Arrays.asList(tmp));
                myReader.close();
            } catch (FileNotFoundException e) {
                System.out.println("An error occurred.");
                e.printStackTrace();
            }
        }
        System.out.println("loaded global partition info");
    }

    public void histogram(GraphLoader graph){//discard super vertex
        System.out.println("Computing Vertex Histogram");

        Map<String, Integer> vertexTypesHistogram = new HashMap<>();
        Map<String, Set<String>> tempVertexAttrFreqMap = new HashMap<>();
        Map<String, Set<String>> attrDistributionMap = new HashMap<>();
        Map<String, List<Integer>> vertexTypesToInDegreesMap = new HashMap<>();
        Map<String, Integer> edgeTypesHistogram = new HashMap<>();

        this.NUM_OF_VERTICES_IN_ALL_GRAPH = readVertexTypesAndAttributeNamesFromGraph(vertexTypesHistogram, tempVertexAttrFreqMap, attrDistributionMap, vertexTypesToInDegreesMap, (GraphLoader) graph);;
        this.NUM_OF_EDGES_IN_ALL_GRAPH = readEdgesInfoFromGraph(edgeTypesHistogram, graph);

        setSortedFrequentVertexTypesHistogram(vertexTypesHistogram);
        setActiveAttributeSet(attrDistributionMap);
        setVertexTypesToAttributesMap(tempVertexAttrFreqMap);

        System.out.println("Number of edges: " + this.NUM_OF_EDGES_IN_ALL_GRAPH);
        System.out.println("Number of edges labels: " + edgeTypesHistogram.size());
        setSortedFrequentEdgeHistogram(edgeTypesHistogram, vertexTypesHistogram);
    }

    private int readVertexTypesAndAttributeNamesFromGraph(Map<String, Integer> vertexTypesHistogram, Map<String, Set<String>> tempVertexAttrFreqMap, Map<String, Set<String>> attrDistributionMap, Map<String, List<Integer>> vertexTypesToInDegreesMap, GraphLoader graph) {
        int numOfVerticesInGraph = 0;
        int numOfAttributesInGraph = 0;
        for (Vertex v: graph.getGraph().getGraph().vertexSet()) {
            numOfVerticesInGraph++;
            for (String vertexType : v.getTypes()) {
                vertexTypesHistogram.merge(vertexType, 1, Integer::sum);
                tempVertexAttrFreqMap.putIfAbsent(vertexType, new HashSet<>());

                for (String attrName: v.getAllAttributesNames()) {
                    if (attrName.equals("uri")) continue;
                    numOfAttributesInGraph++;
                    if (tempVertexAttrFreqMap.containsKey(vertexType)) {
                        tempVertexAttrFreqMap.get(vertexType).add(attrName);
                    }
                    if (!attrDistributionMap.containsKey(attrName)) {
                        attrDistributionMap.put(attrName, new HashSet<>());
                    }
                    attrDistributionMap.get(attrName).add(vertexType);
                }
            }

            int inDegree = graph.getGraph().getGraph().incomingEdgesOf(v).size();
            for (String vertexType: v.getTypes()) {
                if (!vertexTypesToInDegreesMap.containsKey(vertexType)) {
                    vertexTypesToInDegreesMap.put(vertexType, new ArrayList<>());
                }
                vertexTypesToInDegreesMap.get(vertexType).add(inDegree);
            }
        }
        System.out.println("Number of vertices in graph: " + numOfVerticesInGraph);
        System.out.println("Number of attributes in graph: " + numOfAttributesInGraph);
        return numOfVerticesInGraph;
    }

    private int readEdgesInfoFromGraph(Map<String, Integer> edgeTypesHistogram, GraphLoader graph) {
        int numOfEdges = 0;
        for (RelationshipEdge e: graph.getGraph().getGraph().edgeSet()) {
            numOfEdges++;
            Vertex sourceVertex = e.getSource();
            String predicateName = e.getLabel();
            Vertex objectVertex = e.getTarget();
            for (String subjectVertexType: sourceVertex.getTypes()) {
                for (String objectVertexType: objectVertex.getTypes()) {
                    String uniqueEdge = subjectVertexType + " " + predicateName + " " + objectVertexType;
                    edgeTypesHistogram.merge(uniqueEdge, 1, Integer::sum);
                }
            }
        }
        System.out.println("Number of edges in graph: " + numOfEdges);
        return numOfEdges;
    }

    public void setSortedFrequentVertexTypesHistogram(Map<String, Integer> vertexTypesHistogram) {
        ArrayList<Entry<String, Integer>> sortedVertexTypesHistogram = new ArrayList<>(vertexTypesHistogram.entrySet());
        sortedVertexTypesHistogram.sort((o1, o2) -> o2.getValue() - o1.getValue());
        for (Entry<String, Integer> entry : sortedVertexTypesHistogram) {
            this.vertexHistogram.put(entry.getKey(), entry.getValue());
            double vertexFrequency = (double) entry.getValue() / this.NUM_OF_VERTICES_IN_ALL_GRAPH;
            this.vertexFrequenciesList.add(vertexFrequency);
        }
        this.sortedVertexHistogram = sortedVertexTypesHistogram.subList(0, Math.min(sortedVertexTypesHistogram.size(), frequentSetSize));
    }

    private void setActiveAttributeSet(Map<String, Set<String>> attrDistributionMap) {
        ArrayList<Entry<String,Set<String>>> sortedAttrDistributionMap = new ArrayList<>(attrDistributionMap.entrySet());
        sortedAttrDistributionMap.sort((o1, o2) -> o2.getValue().size() - o1.getValue().size());
        HashSet<String> mostDistributedAttributesSet = new HashSet<>();
        for (Entry<String, Set<String>> attrNameEntry : sortedAttrDistributionMap.subList(0, Math.min(this.gamma, sortedAttrDistributionMap.size()))) {
            mostDistributedAttributesSet.add(attrNameEntry.getKey());
        }
        this.activeAttributesSet = mostDistributedAttributesSet;
    }

    private void setVertexTypesToAttributesMap(Map<String, Set<String>> tempVertexAttrFreqMap) {
        Map<String, HashSet<String>> vertexTypesToAttributesMap = new HashMap<>();
        for (String vertexType : tempVertexAttrFreqMap.keySet()) {
            Set<String> attrNameSet = tempVertexAttrFreqMap.get(vertexType);
            vertexTypesToAttributesMap.put(vertexType, new HashSet<>());
            for (String attrName : attrNameSet) {
                if (this.activeAttributesSet.contains(attrName)) {
                    vertexTypesToAttributesMap.get(vertexType).add(attrName);
                }
            }
        }

        this.vertexTypesToAttributesMap = vertexTypesToAttributesMap;
    }

    public void setSortedFrequentEdgeHistogram(Map<String, Integer> edgeTypesHist, Map<String, Integer> vertexTypesHistogram) {
        ArrayList<Entry<String, Integer>> sortedEdgesHist = new ArrayList<>(edgeTypesHist.entrySet());
        sortedEdgesHist.sort((o1, o2) -> o2.getValue() - o1.getValue());
        for (Entry<String, Integer> entry : sortedEdgesHist) {
            String[] edgeString = entry.getKey().split(" ");
            String sourceType = edgeString[0];
            String targetType = edgeString[2];
            this.vertexHistogram.put(sourceType, vertexTypesHistogram.get(sourceType));
            this.vertexHistogram.put(targetType, vertexTypesHistogram.get(targetType));
            double edgeFrequency = (double) entry.getValue() / (double) this.NUM_OF_EDGES_IN_ALL_GRAPH;
            this.edgeFrequenciesList.add(edgeFrequency);
        }
        this.sortedEdgeHistogram = sortedEdgesHist.subList(0, Math.min(sortedEdgesHist.size(), frequentSetSize));
    }

    //TODO: Initialize: vSpawnInit
    public void initialize(GraphLoader graph){//discard tgfd stuff
        vSpawnInit(graph);
        this.patternTree.addLevel();
        this.setCurrentVSpawnLevel(this.getCurrentVSpawnLevel() + 1);
    }

    public void vSpawnInit(GraphLoader graph){
        this.patternTree = new PatternTree();
        this.patternTree.addLevel();
//        System.out.println("VSpawn Level 0");

        for (int i = 0; i < this.sortedVertexHistogram.size(); i++) {
//            System.out.println("VSpawnInit with single-node pattern " + (i+1) + "/" + this.sortedVertexHistogram.size());
            String vertexType = this.sortedVertexHistogram.get(i).getKey();

            if (this.vertexTypesToAttributesMap.get(vertexType).size() < 2)
                continue; // TO-DO: Are we interested in TGFDs where LHS is empty?

            int numOfInstancesOfVertexType = this.sortedVertexHistogram.get(i).getValue();
            int numOfInstancesOfAllVertexTypes = this.NUM_OF_VERTICES_IN_ALL_GRAPH;

            double frequency = (double) numOfInstancesOfVertexType / (double) numOfInstancesOfAllVertexTypes;
//            System.out.println("Frequency of vertex type: " + numOfInstancesOfVertexType + " / " + numOfInstancesOfAllVertexTypes + " = " + frequency);

//            System.out.println("Vertex type: "+vertexType);
            VF2PatternGraph candidatePattern = new VF2PatternGraph();
            PatternVertex vertex = new PatternVertex(vertexType);
            candidatePattern.addVertex(vertex);
            candidatePattern.getCenterVertexType();
//            System.out.println("VSpawnInit with single-node pattern " + (i+1) + "/" + this.sortedVertexHistogram.size() + ": " + candidatePattern.getPattern().vertexSet());

            PatternTreeNode patternTreeNode;
            patternTreeNode = this.patternTree.createNodeAtLevel(this.getCurrentVSpawnLevel(), candidatePattern);

            ArrayList<ArrayList<DataVertex>> matchesOfThisCenterVertexPerTimestamp = extractListOfCenterVertices(graph, vertexType);
            if (this.reUseMatches) {
                patternTreeNode.setListOfCenterVertices(matchesOfThisCenterVertexPerTimestamp);
            }
            int numOfMatches = 0;
            for (ArrayList<DataVertex> matchesOfThisCenterVertex: matchesOfThisCenterVertexPerTimestamp) {
                numOfMatches += matchesOfThisCenterVertex.size();
            }
//            System.out.println("Number of center vertex matches found containing active attributes: " + numOfMatches);
            double estimatePatternSupport = (double) numOfMatches / (double) numOfInstancesOfVertexType;
//            System.out.println("Estimate Pattern Support: " + numOfMatches + " / " + numOfInstancesOfVertexType + " = " + estimatePatternSupport);
            patternTreeNode.setPatternSupport(estimatePatternSupport);
            if (satisfiesTheta(patternTreeNode)) {
                patternTreeNode.setIsPruned();
            }
        }
//        System.out.println("GenTree Level " + this.getCurrentVSpawnLevel() + " size: " + this.patternTree.getLevel(this.getCurrentVSpawnLevel()).size());
        for (PatternTreeNode node : this.patternTree.getLevel(this.getCurrentVSpawnLevel())) {
//            System.out.println("Pattern: " + node.getPattern());
        }
    }

    public int getCurrentVSpawnLevel() {
        return currentVSpawnLevel;
    }

    public void setCurrentVSpawnLevel(int currentVSpawnLevel) {
        this.currentVSpawnLevel = currentVSpawnLevel;
    }

    public ArrayList<ArrayList<DataVertex>> extractListOfCenterVertices(GraphLoader graph, String patternVertexType) {
        ArrayList<ArrayList<DataVertex>> matchesOfThisCenterVertex = new ArrayList<>(1);

        ArrayList<DataVertex> matchesInThisTimestamp = new ArrayList<>();
        for (Vertex vertex : graph.getGraph().getGraph().vertexSet()) {
            if (vertex.getTypes().contains(patternVertexType)) {
                DataVertex dataVertex = (DataVertex) vertex;
                if (this.interestingTGFDs) {
                    // Check if vertex contains at least one active attribute
                    boolean containsActiveAttributes = false;
                    for (String attrName : vertex.getAllAttributesNames()) {
                        if (this.activeAttributesSet.contains(attrName)) {
                            containsActiveAttributes = true;
                            break;
                        }
                    }
                    if (containsActiveAttributes) {
                        matchesInThisTimestamp.add(dataVertex);
                    }
                } else {
                    matchesInThisTimestamp.add(dataVertex);
                }
            }
        }
//        System.out.println("Number of matches found: " + matchesInThisTimestamp.size());
        matchesOfThisCenterVertex.add(matchesInThisTimestamp);
        return matchesOfThisCenterVertex;
    }

    private boolean satisfiesTheta(PatternTreeNode patternTreeNode) {
        return patternTreeNode.getPatternSupport() < this.theta;
    }

    //TODO: Do vSpawn

    public int getK() {
        return k;
    }

    public int getPreviousLevelNodeIndex() {
        return previousLevelNodeIndex;
    }

    public void setPreviousLevelNodeIndex(int previousLevelNodeIndex) {
        this.previousLevelNodeIndex = previousLevelNodeIndex;
    }

    public int getCandidateEdgeIndex() {
        return candidateEdgeIndex;
    }

    public void setCandidateEdgeIndex(int candidateEdgeIndex) {
        this.candidateEdgeIndex = candidateEdgeIndex;
    }

    public boolean hasNoSupportPruning() {
        return this.noSupportPruning;
    }

    public static boolean isDuplicateEdge(VF2PatternGraph pattern, String edgeType, String sourceType, String targetType) {
        for (RelationshipEdge edge : pattern.getPattern().edgeSet()) {
            if (edge.getLabel().equalsIgnoreCase(edgeType)) {
                if (edge.getSource().getTypes().contains(sourceType) && edge.getTarget().getTypes().contains(targetType)) {
                    return true;
                }
            }
        }
        return false;
    }

    public static boolean isMultipleEdge(VF2PatternGraph pattern, String sourceType, String targetType) {
        for (RelationshipEdge edge : pattern.getPattern().edgeSet()) {
            if (edge.getSource().getTypes().contains(sourceType) && edge.getTarget().getTypes().contains(targetType)) {
                return true;
            }
        }
        return false;
    }

    private PatternVertex isDuplicateVertex(VF2PatternGraph newPattern, String vertexType) {
        for (Vertex v: newPattern.getPattern().vertexSet()) {
            if (v.getTypes().contains(vertexType)) {
                return (PatternVertex) v;
            }
        }
        return null;
    }

    private boolean isIsomorphicPattern(VF2PatternGraph newPattern, PatternTree patternTree) {
//        System.out.println("Checking if following pattern is isomorphic\n" + newPattern);
        ArrayList<String> newPatternEdges = new ArrayList<>();
        newPattern.getPattern().edgeSet().forEach((edge) -> {newPatternEdges.add(edge.toString());});
        boolean isIsomorphic = false;
        for (PatternTreeNode otherPattern: patternTree.getLevel(this.getCurrentVSpawnLevel())) {
            ArrayList<String> otherPatternEdges = new ArrayList<>();
            otherPattern.getGraph().edgeSet().forEach((edge) -> {otherPatternEdges.add(edge.toString());});
            if (newPatternEdges.containsAll(otherPatternEdges)) {
//                System.out.println("Candidate pattern: " + newPattern);
//                System.out.println("is an isomorph of current VSpawn level pattern: " + otherPattern.getPattern());
                isIsomorphic = true;
            }
        }
        return isIsomorphic;
    }

    private boolean isSuperGraphOfPrunedPattern(VF2PatternGraph newPattern, PatternTree patternTree) {
        ArrayList<String> newPatternEdges = new ArrayList<>();
        newPattern.getPattern().edgeSet().forEach((edge) -> {newPatternEdges.add(edge.toString());});
        int i = this.getCurrentVSpawnLevel();
        boolean isSupergraph = false;
        while (i > 0) {
            for (PatternTreeNode otherPattern : patternTree.getLevel(i)) {
                if (otherPattern.isPruned()) {
                    ArrayList<String> otherPatternEdges = new ArrayList<>();
                    otherPattern.getGraph().edgeSet().forEach((edge) -> {otherPatternEdges.add(edge.toString());});
                    if (newPatternEdges.containsAll(otherPatternEdges)) {
//                        System.out.println("Candidate pattern: " + newPattern);
//                        System.out.println("is a superset of pruned subgraph pattern: " + otherPattern.getPattern());
                        isSupergraph = true;
                    }
                }
            }
            i--;
        }
        return isSupergraph;
    }

    public PatternTreeNode vSpawn(){
        if (this.getCandidateEdgeIndex() > this.sortedEdgeHistogram.size()-1) {
            this.setCandidateEdgeIndex(0);
            this.setPreviousLevelNodeIndex(this.getPreviousLevelNodeIndex() + 1);
        }
        if (this.getPreviousLevelNodeIndex() >= this.patternTree.getLevel(this.getCurrentVSpawnLevel() -1).size()) {
            this.setCurrentVSpawnLevel(this.getCurrentVSpawnLevel() + 1);
            if (this.getCurrentVSpawnLevel() > this.getK()) {
                return null;
            }
            this.patternTree.addLevel();
            this.setPreviousLevelNodeIndex(0);
            this.setCandidateEdgeIndex(0);
        }
//        System.out.println("Performing VSpawn");
//        System.out.println("VSpawn Level " + this.getCurrentVSpawnLevel());
        ArrayList<PatternTreeNode> previousLevel = this.patternTree.getLevel(this.getCurrentVSpawnLevel() - 1);
        if (previousLevel.size() == 0) {
            this.setPreviousLevelNodeIndex(this.getPreviousLevelNodeIndex() + 1);
            return null;
        }
        PatternTreeNode previousLevelNode = previousLevel.get(this.getPreviousLevelNodeIndex());
//        System.out.println("Processing previous level node " + this.getPreviousLevelNodeIndex() + "/" + previousLevel.size());
//        System.out.println("Performing VSpawn on pattern: " + previousLevelNode.getPattern());
//
//        System.out.println("Level " + (this.getCurrentVSpawnLevel() - 1) + " pattern: " + previousLevelNode.getPattern());
        if (!this.hasNoSupportPruning() && previousLevelNode.isPruned()) {
//            System.out.println("Marked as pruned. Skip.");
            this.setPreviousLevelNodeIndex(this.getPreviousLevelNodeIndex() + 1);
            return null;
        }
//        System.out.println("Processing candidate edge " + this.getCandidateEdgeIndex() + "/" + this.sortedEdgeHistogram.size());
        Entry<String, Integer> candidateEdge = this.sortedEdgeHistogram.get(this.getCandidateEdgeIndex());
        String candidateEdgeString = candidateEdge.getKey();
//        System.out.println("Candidate edge:" + candidateEdgeString);


        String sourceVertexType = candidateEdgeString.split(" ")[0];
        String targetVertexType = candidateEdgeString.split(" ")[2];

        if (this.vertexTypesToAttributesMap.get(targetVertexType).size() == 0) {
//            System.out.println("Target vertex in candidate edge does not contain active attributes");
            this.setCandidateEdgeIndex(this.getCandidateEdgeIndex() + 1);
            return null;
        }
        if (sourceVertexType.equals(targetVertexType)) {
//            System.out.println("Candidate edge contains duplicate vertex types. Skip.");
            this.setCandidateEdgeIndex(this.getCandidateEdgeIndex() + 1);
            return null;
        }
        String edgeType = candidateEdgeString.split(" ")[1];
        // Check if candidate edge already exists in pattern
        if (isDuplicateEdge(previousLevelNode.getPattern(), edgeType, sourceVertexType, targetVertexType)) {
//            System.out.println("Candidate edge: " + candidateEdge.getKey());
//            System.out.println("already exists in pattern");
            this.setCandidateEdgeIndex(this.getCandidateEdgeIndex() + 1);
            return null;
        }

        if (isMultipleEdge(previousLevelNode.getPattern(), sourceVertexType, targetVertexType)) {
//            System.out.println("We do not support multiple edges between existing vertices.");
            this.setCandidateEdgeIndex(this.getCandidateEdgeIndex() + 1);
            return null;
        }

        // Checks if candidate edge extends pattern
        PatternVertex sourceVertex = isDuplicateVertex(previousLevelNode.getPattern(), sourceVertexType);
        PatternVertex targetVertex = isDuplicateVertex(previousLevelNode.getPattern(), targetVertexType);
        if (sourceVertex == null && targetVertex == null) {
//            System.out.println("Candidate edge: " + candidateEdge.getKey());
//            System.out.println("does not extend from pattern");
            this.setCandidateEdgeIndex(this.getCandidateEdgeIndex() + 1);
            return null;
        }

        PatternTreeNode patternTreeNode = null;
        // TO-DO: FIX label conflict. What if an edge has same vertex type on both sides?
        for (Vertex v : previousLevelNode.getGraph().vertexSet()) {
//            System.out.println("Looking to add candidate edge to vertex: " + v.getTypes());

            if (v.isMarked()) {
//                System.out.println("Skip vertex. Already added candidate edge to vertex: " + v.getTypes());
                continue;
            }
            if (!v.getTypes().contains(sourceVertexType) && !v.getTypes().contains(targetVertexType)) {
//                System.out.println("Skip vertex. Candidate edge does not connect to vertex: " + v.getTypes());
                v.setMarked(true);
                continue;
            }

            // Create unmarked copy of k-1 pattern
            VF2PatternGraph newPattern = previousLevelNode.getPattern().copy();
            if (targetVertex == null) {
                targetVertex = new PatternVertex(targetVertexType);
                newPattern.addVertex(targetVertex);
            } else {
                for (Vertex vertex : newPattern.getPattern().vertexSet()) {
                    if (vertex.getTypes().contains(targetVertexType)) {
                        targetVertex.setMarked(true);
                        targetVertex = (PatternVertex) vertex;
                        break;
                    }
                }
            }
            RelationshipEdge newEdge = new RelationshipEdge(edgeType);
            if (sourceVertex == null) {
                sourceVertex = new PatternVertex(sourceVertexType);
                newPattern.addVertex(sourceVertex);
            } else {
                for (Vertex vertex : newPattern.getPattern().vertexSet()) {
                    if (vertex.getTypes().contains(sourceVertexType)) {
                        sourceVertex.setMarked(true);
                        sourceVertex = (PatternVertex) vertex;
                        break;
                    }
                }
            }
            newPattern.addEdge(sourceVertex, targetVertex, newEdge);

//            System.out.println("Created new pattern: " + newPattern);

            // TO-DO: Debug - Why does this work with strings but not subgraph isomorphism???
            if (isIsomorphicPattern(newPattern, this.patternTree)) {
                v.setMarked(true);
//                System.out.println("Skip. Candidate pattern is an isomorph of existing pattern");
                continue;
            }

            if (!this.hasNoSupportPruning() && isSuperGraphOfPrunedPattern(newPattern, this.patternTree)) {
                v.setMarked(true);
//                System.out.println("Skip. Candidate pattern is a supergraph of pruned pattern");
                continue;
            }
            patternTreeNode = this.patternTree.createNodeAtLevel(this.getCurrentVSpawnLevel(), newPattern, previousLevelNode, candidateEdgeString);
//            System.out.println("Marking vertex " + v.getTypes() + "as expanded.");
            break;
        }
        if (patternTreeNode == null) {
            for (Vertex v : previousLevelNode.getGraph().vertexSet()) {
//                System.out.println("Unmarking all vertices in current pattern for the next candidate edge");
                v.setMarked(false);
            }
            this.setCandidateEdgeIndex(this.getCandidateEdgeIndex() + 1);
        }
        return patternTreeNode;
    }

    //TODO: Do match
    public boolean isSkipK1() {
        return skipK1;
    }

    public void findMatchesUsingCenterVertices(GraphLoader graph, PatternTreeNode patternTreeNode, ArrayList<HashSet<ConstantLiteral>> matches) {
        HashSet<String> entityURIs = new HashSet<>();
        extractMatchesAcrossSnapshots(graph, patternTreeNode, matches, entityURIs);
        System.out.println("Total number of matches founded for this pattern:" + matches.size());
        System.out.println("An example for match: ");
        if(matches.size() != 0){
            for(ConstantLiteral m:matches.get(0)){
                System.out.print(m.toString() + " ");
            }
            System.out.println(" ");
        }
//        //tmp banned
//        if (!this.useChangeFile) {
//            calculatePatternSupport(entityURIs.size(), patternTreeNode);
//        }
    }
    public int getDistance(String v1, String v2, Graph<Vertex,RelationshipEdge> g){
//        let Q be a queue
//              label root as explored
//              Q.enqueue(root)
//              while Q is not empty do
//                      v := Q.dequeue()
//                  if v is the goal then
//                      return v
//                  for all edges from v to w in G.adjacentEdges(v) do
//                          if w is not labeled as explored then
//                          label w as explored
//                          Q.enqueue(w)
        HashMap <String,Integer> visited=new HashMap<>();

        LinkedList <String> queue = new LinkedList<>();
        int d=Integer.MAX_VALUE;
        visited.put(v1,0);
        queue.add(v1);
        String x;
//        while (queue.size() != 0) {
//            x = queue.poll();
//            int distance = visited.get(x);
//            for (RelationshipEdge edge : g.edgesOf(Vertex x = new String(x))) {
//                w = edge.getSource();
//                if (w.equals(x)) w = edge.getTarget();
//                if (!visited.containsKey(w)) {
//                    d = distance + 1;
//                    visited.put(w, distance + 1);
//                    queue.add(w);
//                }
//            }
//        }
        return d;
    }
    private void extractMatchesAcrossSnapshots(GraphLoader graph, PatternTreeNode patternTreeNode, ArrayList<HashSet<ConstantLiteral>> matchesPerTimestamps, HashSet<String> entityURIs) {
        //TODO: matchSet, reuseMatch
        //--------
        String originalCenter = patternTreeNode.getPattern().getCenterVertexType();
        int[] dist = new int[4];
        String[] center = new String[4];
        for(int d : dist){
            d = Integer.MAX_VALUE;
        }
        for(Vertex v:patternTreeNode.getPattern().getPattern().vertexSet()){
            for(String ty:v.getTypes()){
                for(int i=0;i<4;i++){
                    if(vertexOnMachine.get(i).contains(ty)){
                        int temp = getDistance(ty,originalCenter,patternTreeNode.getPattern().getPattern());
                        if(temp < dist[i]){
                            center[i] = ty;
                            dist[i] = temp;
                        }
                    }
                }
            }
        }
        //--------
        ArrayList<ArrayList<DataVertex>> matchesOfCenterVertex = extractListOfCenterVertices(graph, center[0]);
        //temp
//        ArrayList<ArrayList<DataVertex>> matchesOfCenterVertex = getListOfMatchesOfCenterVerticesOfThisPattern(graph, patternTreeNode);

        ArrayList<DataVertex> newMatchesOfCenterVertexInCurrentSnapshot = new ArrayList<>();

//        int diameter = patternTreeNode.getPattern().getDiameter();
//        System.out.println("Searching for patterns of diameter: " + diameter);

        HashSet<HashSet<ConstantLiteral>> matchesSet = new HashSet<>();
//        System.out.println("Number of center vertex matches in this timestamp from previous levels: "+matchesOfCenterVertex.get(0).size());

        int numOfMatchesInTimestamp = 0; int processedCount = 0;
        for (DataVertex dataVertex: matchesOfCenterVertex.get(0)) {
            int numOfMatchesFound = 0;
            if (this.getCurrentVSpawnLevel() == 1) {
                numOfMatchesFound = findAllMatchesOfEdgeInSnapshotUsingCenterVertices(patternTreeNode, entityURIs, graph, matchesSet, newMatchesOfCenterVertexInCurrentSnapshot, dataVertex);
            } else {
//                numOfMatchesFound = findAllMatchesOfPatternInThisSnapshotUsingCenterVertices(patternTreeNode, entityURIs, graph, matchesSet, newMatchesOfCenterVertexInCurrentSnapshot, dataVertex);
                for(String ty:dataVertex.getTypes()){
                    if(vertexOnMachine.get(0).contains(ty)){
                        numOfMatchesFound = findPartialMatch(vertexOnMachine.get(0), patternTreeNode, entityURIs, graph, matchesSet, newMatchesOfCenterVertexInCurrentSnapshot, dataVertex);
                    }
                }
            }
            numOfMatchesInTimestamp += numOfMatchesFound;

            processedCount++;
            if (matchesOfCenterVertex.size() >= 100000 && processedCount % 100000 == 0) {
                System.out.println("Processed " + processedCount + "/" + matchesOfCenterVertex.size());
            }
        }
//        System.out.println("Number of matches found: " + numOfMatchesInTimestamp);
        System.out.println("Number of matches found that contain active attributes: " + matchesSet.size());
//        System.out.println("Number of center vertex matches in this timestamp in this level: " + newMatchesOfCenterVertexInCurrentSnapshot.size());
        matchesPerTimestamps.addAll(matchesSet);

        if (this.isReUseMatches()) {
            ArrayList<ArrayList<DataVertex>> newMatchesOfCenterVerticesInAllSnapshots = new ArrayList<>();
            newMatchesOfCenterVerticesInAllSnapshots.add(newMatchesOfCenterVertexInCurrentSnapshot);
            patternTreeNode.setListOfCenterVertices(newMatchesOfCenterVerticesInAllSnapshots);
        }
    }

    private ArrayList<ArrayList<DataVertex>> getListOfMatchesOfCenterVerticesOfThisPattern(GraphLoader graph, PatternTreeNode patternTreeNode) {
        String centerVertexType = patternTreeNode.getPattern().getCenterVertexType();
        PatternTreeNode centerVertexParent = patternTreeNode.getCenterVertexParent();
//        System.out.println("Center vertex type: "+centerVertexType);
        ArrayList<ArrayList<DataVertex>> matchesOfCenterVertex;
        if (centerVertexParent != null && centerVertexParent.getListOfCenterVertices() != null) {
            matchesOfCenterVertex = centerVertexParent.getListOfCenterVertices();
        } else {
            matchesOfCenterVertex = extractListOfCenterVertices(graph, centerVertexType);
        }
        return matchesOfCenterVertex;
    }

    private int findAllMatchesOfEdgeInSnapshotUsingCenterVertices(PatternTreeNode patternTreeNode, HashSet<String> entityURIs, GraphLoader currentSnapshot, HashSet<HashSet<ConstantLiteral>> matchesSet, ArrayList<DataVertex> matchesOfCenterVertexInCurrentSnapshot, DataVertex dataVertex) {
        String centerVertexType = patternTreeNode.getPattern().getCenterVertexType();
        Set<String> edgeLabels = patternTreeNode.getGraph().edgeSet().stream().map(RelationshipEdge::getLabel).collect(Collectors.toSet());
        String sourceType = patternTreeNode.getGraph().edgeSet().iterator().next().getSource().getTypes().iterator().next();
        String targetType = patternTreeNode.getGraph().edgeSet().iterator().next().getTarget().getTypes().iterator().next();

        Set<RelationshipEdge> edgeSet;
        if (centerVertexType.equals(sourceType)) {
            edgeSet = currentSnapshot.getGraph().getGraph().outgoingEdgesOf(dataVertex).stream().filter(e -> edgeLabels.contains(e.getLabel()) && e.getTarget().getTypes().contains(targetType)).collect(Collectors.toSet());
        } else {
            edgeSet = currentSnapshot.getGraph().getGraph().incomingEdgesOf(dataVertex).stream().filter(e -> edgeLabels.contains(e.getLabel()) && e.getSource().getTypes().contains(sourceType)).collect(Collectors.toSet());
        }

        ArrayList<HashSet<ConstantLiteral>> matches = new ArrayList<>();
        int numOfMatchesFound = extractMatches(edgeSet, matches, patternTreeNode, entityURIs);
        if (numOfMatchesFound > 0) { // equivalent to results.isomorphismExists()
            matchesSet.addAll(matches);
            matchesOfCenterVertexInCurrentSnapshot.add(dataVertex);
            //new show up
//            for(HashSet<ConstantLiteral> eachMatches : matchesSet){
//                System.out.print("An example for match is: ");
//                for(ConstantLiteral lit : eachMatches){
//                    System.out.print(lit.toString()+" ");
//                }
//                System.out.println(" ");
//                break;
//            }
        }
        return numOfMatchesFound;
    }

    public int extractMatches(Set<RelationshipEdge> edgeSet, ArrayList<HashSet<ConstantLiteral>> matches, PatternTreeNode patternTreeNode, HashSet<String> entityURIs) {
        String patternEdgeLabel = patternTreeNode.getGraph().edgeSet().iterator().next().getLabel();
        String sourceVertexType = patternTreeNode.getGraph().edgeSet().iterator().next().getSource().getTypes().iterator().next();
        String targetVertexType = patternTreeNode.getGraph().edgeSet().iterator().next().getTarget().getTypes().iterator().next();
        int numOfMatches = 0;
        for (RelationshipEdge edge: edgeSet) {
            String matchedEdgeLabel = edge.getLabel();
            Set<String> matchedSourceVertexType = edge.getSource().getTypes();
            Set<String> matchedTargetVertexType = edge.getTarget().getTypes();
            if (matchedEdgeLabel.equals(patternEdgeLabel) && matchedSourceVertexType.contains(sourceVertexType) && matchedTargetVertexType.contains(targetVertexType)) {
                numOfMatches++;
                HashSet<ConstantLiteral> literalsInMatch = new HashSet<>();
                extractMatch(edge.getSource(), sourceVertexType, edge.getTarget(), targetVertexType, patternTreeNode, literalsInMatch, entityURIs);
                if (this.interestingTGFDs) {
                    int interestingLiteralCount = 0;
                    for (ConstantLiteral literal: literalsInMatch) {
                        if (!literal.getAttrName().equals("uri")) {
                            interestingLiteralCount++;
                        }
                        if (interestingLiteralCount >= patternTreeNode.getGraph().vertexSet().size()) {
                            break;
                        }
                    }
                    if (interestingLiteralCount < patternTreeNode.getGraph().vertexSet().size()) continue;
                } else {
                    if (literalsInMatch.size() <= patternTreeNode.getGraph().vertexSet().size()) continue;
                }
                matches.add(literalsInMatch);
            }
        }
        matches.sort(new Comparator<HashSet<ConstantLiteral>>() {
            @Override
            public int compare(HashSet<ConstantLiteral> o1, HashSet<ConstantLiteral> o2) {
                return o1.size() - o2.size();
            }
        });
        return numOfMatches;
    }

    private void extractMatch(Vertex currentSourceVertex, String sourceVertexType, Vertex currentTargetVertex, String targetVertexType, PatternTreeNode patternTreeNode, HashSet<ConstantLiteral> match, HashSet<String> entityURIs) {
        String entityURI = null;
        List<String> patternVerticesTypes = Arrays.asList(sourceVertexType, targetVertexType);
        List<Vertex> vertices = Arrays.asList(currentSourceVertex, currentTargetVertex);
        for (int index = 0; index < vertices.size(); index++) {
            Vertex currentMatchedVertex = vertices.get(index);
            String patternVertexType = patternVerticesTypes.get(index);
            if (entityURI == null) {
                entityURI = extractAttributes(patternTreeNode, patternVertexType, match, currentMatchedVertex);
            } else {
                extractAttributes(patternTreeNode, patternVertexType, match, currentMatchedVertex);
            }
        }
        if (entityURI != null && match.size() > patternTreeNode.getGraph().vertexSet().size()) {
            entityURIs.add(entityURI);
        }
    }

    private String extractAttributes(PatternTreeNode patternTreeNode, String patternVertexType, HashSet<ConstantLiteral> match, Vertex currentMatchedVertex) {
        String entityURI = null;
        String centerVertexType = patternTreeNode.getPattern().getCenterVertexType();
        Set<String> matchedVertexTypes = currentMatchedVertex.getTypes();
        for (ConstantLiteral activeAttribute : getActiveAttributesInPattern(patternTreeNode.getGraph().vertexSet(),true)) {
            if (!matchedVertexTypes.contains(activeAttribute.getVertexType())) continue;
            for (String matchedAttrName : currentMatchedVertex.getAllAttributesNames()) {
                if (matchedVertexTypes.contains(centerVertexType) && matchedAttrName.equals("uri")) {
                    entityURI = currentMatchedVertex.getAttributeValueByName(matchedAttrName);
                }
                if (!activeAttribute.getAttrName().equals(matchedAttrName)) continue;
                String matchedAttrValue = currentMatchedVertex.getAttributeValueByName(matchedAttrName);
                ConstantLiteral xLiteral = new ConstantLiteral(patternVertexType, matchedAttrName, matchedAttrValue);
                match.add(xLiteral);
            }
        }
        return entityURI;
    }

    public HashSet<ConstantLiteral> getActiveAttributesInPattern(Set<Vertex> vertexSet, boolean considerURI) {
        HashMap<String, HashSet<String>> patternVerticesAttributes = new HashMap<>();
        for (Vertex vertex : vertexSet) {
            for (String vertexType : vertex.getTypes()) {
                patternVerticesAttributes.put(vertexType, new HashSet<>());
                Set<String> attrNameSet = this.vertexTypesToAttributesMap.get(vertexType);
                for (String attrName : attrNameSet) {
                    patternVerticesAttributes.get(vertexType).add(attrName);
                }
            }
        }
        HashSet<ConstantLiteral> literals = new HashSet<>();
        for (String vertexType : patternVerticesAttributes.keySet()) {
            if (considerURI) literals.add(new ConstantLiteral(vertexType,"uri",null));
            for (String attrName : patternVerticesAttributes.get(vertexType)) {
                ConstantLiteral literal = new ConstantLiteral(vertexType, attrName, null);
                literals.add(literal);
            }
        }
        return literals;
    }

    private int findAllMatchesOfPatternInThisSnapshotUsingCenterVertices(PatternTreeNode patternTreeNode, HashSet<String> entityURIs, GraphLoader currentSnapshot, HashSet<HashSet<ConstantLiteral>> matchesSet, ArrayList<DataVertex> matchesOfCenterVertexInCurrentSnapshot, DataVertex dataVertex) {
        Set<String> edgeLabels = patternTreeNode.getGraph().edgeSet().stream().map(RelationshipEdge::getLabel).collect(Collectors.toSet());
        int diameter = patternTreeNode.getPattern().getDiameter();
        Graph<Vertex, RelationshipEdge> subgraph = currentSnapshot.getGraph().getSubGraphWithinDiameter(dataVertex, diameter, edgeLabels, patternTreeNode.getGraph().edgeSet());
        VF2AbstractIsomorphismInspector<Vertex, RelationshipEdge> results = new VF2SubgraphIsomorphism().execute2(subgraph, patternTreeNode.getPattern(), false);

        int numOfMatchesForCenterVertex = 0;
        ArrayList<HashSet<ConstantLiteral>> matches = new ArrayList<>();
        if (results.isomorphismExists()) {
            numOfMatchesForCenterVertex = extractMatches(results.getMappings(), matches, patternTreeNode, entityURIs);
            matchesSet.addAll(matches);
            matchesOfCenterVertexInCurrentSnapshot.add(dataVertex);
            //new show up
//            for(HashSet<ConstantLiteral> eachMatches : matchesSet){
//                System.out.print("An example for match is: ");
//                for(ConstantLiteral lit : eachMatches){
//                    System.out.print(lit.toString()+" ");
//                }
//                System.out.println(" ");
//                break;
//            }
        }

        return numOfMatchesForCenterVertex;
    }

    private int findPartialMatch(Set<String> vertexOnMachine, PatternTreeNode patternTreeNode, HashSet<String> entityURIs, GraphLoader currentSnapshot, HashSet<HashSet<ConstantLiteral>> matchesSet, ArrayList<DataVertex> matchesOfCenterVertexInCurrentSnapshot, DataVertex dataVertex) {
        Set<Vertex> vertexSet = patternTreeNode.getGraph().vertexSet();
        Set<Vertex> subVertexSet = new HashSet<>();
        for(Vertex v:vertexSet){
            for(String type:v.getTypes()){
                if(vertexOnMachine.contains(type)){
                    subVertexSet.add(v);
                }
            }
        }
        Set<RelationshipEdge> edgeSet = patternTreeNode.getGraph().edgeSet();
        Set<RelationshipEdge> subEdgeSet = new HashSet<>();
        for(RelationshipEdge e : edgeSet){
            if(subVertexSet.contains(e.getSource()) && subVertexSet.contains(e.getTarget())){
                subEdgeSet.add(e);
            }
        }

        Set<String> edgeLabels = subEdgeSet.stream().map(RelationshipEdge::getLabel).collect(Collectors.toSet());
        VF2PatternGraph newPatternTreeNode = new VF2PatternGraph();
        for (Vertex v : subVertexSet) {
            PatternVertex newV = ((PatternVertex) v).copy();
            newPatternTreeNode.addVertex(newV);
        }
        for (RelationshipEdge e : subEdgeSet) {
            PatternVertex source = null;
            for (Vertex vertex : newPatternTreeNode.getPattern().vertexSet()) {
                if (vertex.getTypes().contains(new ArrayList<>(((PatternVertex) e.getSource()).getTypes()).get(0))) {
                    source = (PatternVertex) vertex;
                }
            }
            PatternVertex target = null;
            for (Vertex vertex : newPatternTreeNode.getPattern().vertexSet()) {
                if (vertex.getTypes().contains(new ArrayList<>(((PatternVertex) e.getTarget()).getTypes()).get(0))) {
                    target = (PatternVertex) vertex;
                }
            }
            newPatternTreeNode.addEdge(source, target, new RelationshipEdge(e.getLabel()));
        }
        newPatternTreeNode.setDiameter(subVertexSet.size() - 1);


        Graph<Vertex, RelationshipEdge> subgraph = currentSnapshot.getGraph().getSubGraphWithinDiameter(dataVertex, newPatternTreeNode.getDiameter(), edgeLabels, subEdgeSet);
        VF2AbstractIsomorphismInspector<Vertex, RelationshipEdge> results = new VF2SubgraphIsomorphism().execute2(subgraph, newPatternTreeNode, false);

        int numOfMatches = 0;
        ArrayList<HashSet<ConstantLiteral>> partialMatches = new ArrayList<>();
        if (results.isomorphismExists()) {
            numOfMatches = extractMatches(results.getMappings(), partialMatches, patternTreeNode, entityURIs);
            matchesSet.addAll(partialMatches);
            matchesOfCenterVertexInCurrentSnapshot.add(dataVertex);
            //new show up
            for(HashSet<ConstantLiteral> eachMatches : partialMatches){
                System.out.print("An example for partial match is: ");
                for(ConstantLiteral lit : eachMatches){
                    System.out.print(lit.toString()+" ");
                }
                System.out.println(" ");
                break;
            }
        }
        return numOfMatches;
    }

    private int extractMatches(Iterator<GraphMapping<Vertex, RelationshipEdge>> iterator, ArrayList<HashSet<ConstantLiteral>> matches, PatternTreeNode patternTreeNode, HashSet<String> entityURIs) {
        int numOfMatches = 0;
        while (iterator.hasNext()) {
            numOfMatches++;
            GraphMapping<Vertex, RelationshipEdge> result = iterator.next();
            HashSet<ConstantLiteral> match = new HashSet<>();
            extractMatch(result, patternTreeNode, match, entityURIs);
            // ensures that the match is not empty and contains more than just the uri attribute
            if (match.size() <= patternTreeNode.getGraph().vertexSet().size()) continue;
            matches.add(match);
        }
        matches.sort(new Comparator<HashSet<ConstantLiteral>>() {
            @Override
            public int compare(HashSet<ConstantLiteral> o1, HashSet<ConstantLiteral> o2) {
                return o1.size() - o2.size();
            }
        });
        return numOfMatches;
    }

    private void extractMatch(GraphMapping<Vertex, RelationshipEdge> result, PatternTreeNode patternTreeNode, HashSet<ConstantLiteral> match, HashSet<String> entityURIs) {
        String entityURI = null;
        for (Vertex v : patternTreeNode.getGraph().vertexSet()) {
            Vertex currentMatchedVertex = result.getVertexCorrespondence(v, false);
            if (currentMatchedVertex == null) continue;
            String patternVertexType = v.getTypes().iterator().next();
            if (entityURI == null) {
                entityURI = extractAttributes(patternTreeNode, patternVertexType, match, currentMatchedVertex);
            } else {
                extractAttributes(patternTreeNode, patternVertexType, match, currentMatchedVertex);
            }
        }
        if (entityURI != null && match.size() > patternTreeNode.getGraph().vertexSet().size()) {
            entityURIs.add(entityURI);
        }
    }

    public boolean isReUseMatches() {
        return reUseMatches;
    }

    private void calculatePatternSupport(int numberOfEntitiesFound, PatternTreeNode patternTreeNode) {
        String centerVertexType = patternTreeNode.getPattern().getCenterVertexType();
        System.out.println("Center vertex type: " + centerVertexType);
        double s = this.vertexHistogram.get(centerVertexType);
        double numerator = 2 * numberOfEntitiesFound * this.numOfSnapshots;
        double denominator = (2 * s * this.numOfSnapshots);
        assert numerator <= denominator;
        double realPatternSupport = numerator / denominator;
        System.out.println("Real Pattern Support: "+numerator+" / "+denominator+" = " + realPatternSupport);
        patternTreeNode.setPatternSupport(realPatternSupport);
        this.patternSupportsList.add(realPatternSupport);
    }

    //TODO: hSpawn
    public ArrayList<TGFD> hSpawn(PatternTreeNode patternTreeNode, ArrayList<HashSet<ConstantLiteral>> matchesPerTimestamps) {
        ArrayList<TGFD> tgfds = new ArrayList<>();

        System.out.println("Performing HSpawn for " + patternTreeNode.getPattern());

        HashSet<ConstantLiteral> activeAttributes = getActiveAttributesInPattern(patternTreeNode.getGraph().vertexSet(), false);

        LiteralTree literalTree = new LiteralTree();
        for (int j = 0; j < activeAttributes.size(); j++) {

            System.out.println("HSpawn level " + j + "/" + activeAttributes.size());

            if (j == 0) {
                literalTree.addLevel();
                for (ConstantLiteral literal: activeAttributes) {
                    literalTree.createNodeAtLevel(j, literal, null);
                }
            } else if ((j + 1) <= patternTreeNode.getGraph().vertexSet().size()) { // Ensures # of literals in dependency equals number of vertices in graph
                ArrayList<LiteralTreeNode> literalTreePreviousLevel = literalTree.getLevel(j - 1);
                if (literalTreePreviousLevel.size() == 0) {
//                    System.out.println("Previous level of literal tree is empty. Nothing to expand. End HSpawn");
                    break;
                }
                literalTree.addLevel();
                ArrayList<AttributeDependency> visitedPaths = new ArrayList<>(); //TO-DO: Can this be implemented as HashSet to improve performance?
                ArrayList<TGFD> currentLevelTGFDs = new ArrayList<>();
                for (LiteralTreeNode previousLevelLiteral : literalTreePreviousLevel) {
//                    System.out.println("Creating literal tree node " + literalTree.getLevel(j).size() + "/" + (literalTreePreviousLevel.size() * (literalTreePreviousLevel.size()-1)));
                    if (previousLevelLiteral.isPruned()) continue;
                    ArrayList<ConstantLiteral> parentsPathToRoot = previousLevelLiteral.getPathToRoot(); //TO-DO: Can this be implemented as HashSet to improve performance?
                    for (ConstantLiteral literal: activeAttributes) {
                        if (this.interestingTGFDs) { // Ensures all vertices are involved in dependency
                            if (isUsedVertexType(literal.getVertexType(), parentsPathToRoot)) continue;
                        } else { // Check if leaf node exists in path already
                            if (parentsPathToRoot.contains(literal)) continue;
                        }

                        // Check if path to candidate leaf node is unique
                        AttributeDependency newPath = new AttributeDependency(previousLevelLiteral.getPathToRoot(),literal);
                        System.out.println("New candidate literal path: " + newPath);
                        if (isPathVisited(newPath, visitedPaths)) { // TO-DO: Is this relevant anymore?
//                            System.out.println("Skip. Duplicate literal path.");
                            continue;
                        }

                        if (!this.hasNoSupportPruning() && isSupersetPath(newPath, patternTreeNode.getLowSupportDependenciesOnThisPath())) { // Ensures we don't re-explore dependencies whose subsets have no entities
//                            System.out.println("Skip. Candidate literal path is a superset of low-support dependency.");
                            continue;
                        }
                        if (!this.noMinimalityPruning && isSupersetPath(newPath, patternTreeNode.getAllMinimalDependenciesOnThisPath())) { // Ensures we don't re-explore dependencies whose subsets have already have a general dependency
//                            System.out.println("Skip. Candidate literal path is a superset of minimal dependency.");
                            continue;
                        }
                        System.out.println("Newly created unique literal path: " + newPath);

                        // Add leaf node to tree
                        LiteralTreeNode literalTreeNode = literalTree.createNodeAtLevel(j, literal, previousLevelLiteral);

                        // Ensures delta discovery only occurs when # of literals in dependency equals number of vertices in graph
                        if (this.interestingTGFDs && (j + 1) != patternTreeNode.getGraph().vertexSet().size()) {
//                            System.out.println("|LHS|+|RHS| != |Q|. Skip performing Delta Discovery HSpawn level " + j);
                            continue;
                        }
                        visitedPaths.add(newPath);

                        System.out.println("Performing Delta Discovery at HSpawn level " + j);
                        final long deltaDiscoveryTime = System.currentTimeMillis();
                        ArrayList<TGFD> discoveredTGFDs = deltaDiscovery(patternTreeNode, literalTreeNode, newPath, matchesPerTimestamps);
//                        printWithTime("deltaDiscovery", System.currentTimeMillis()-deltaDiscoveryTime);
                        long deltaTime = System.currentTimeMillis()-deltaDiscoveryTime;
                        System.out.println("deltaTime"+deltaTime);
                        currentLevelTGFDs.addAll(discoveredTGFDs);
                    }
                }
                if (currentLevelTGFDs.size() > 0) {
                    System.out.println("TGFDs generated at HSpawn level " + j + ": " + currentLevelTGFDs.size());
                    tgfds.addAll(currentLevelTGFDs);
                }
            } else {
                break;
            }
//            System.out.println("Generated new literal tree nodes: "+ literalTree.getLevel(j).size());
        }
        System.out.println("For pattern " + patternTreeNode.getPattern());
        System.out.println("HSpawn TGFD count: " + tgfds.size());
        return tgfds;
    }

    private static boolean isUsedVertexType(String vertexType, ArrayList<ConstantLiteral> parentsPathToRoot) {
        for (ConstantLiteral literal : parentsPathToRoot) {
            if (literal.getVertexType().equals(vertexType)) {
                return true;
            }
        }
        return false;
    }

    public boolean isPathVisited(AttributeDependency path, ArrayList<AttributeDependency> visitedPaths) {
        long visitedPathCheckingTime = System.currentTimeMillis();
        for (AttributeDependency visitedPath : visitedPaths) {
            if (visitedPath.size() == path.size()
                    && visitedPath.getLhs().containsAll(path.getLhs())
                    && visitedPath.getRhs().equals(path.getRhs())) {
//                System.out.println("This literal path was already visited.");
                return true;
            }
        }
        visitedPathCheckingTime = System.currentTimeMillis() - visitedPathCheckingTime;
//        printWithTime("visitedPathCheckingTime", visitedPathCheckingTime);
//        totalVisitedPathCheckingTime += visitedPathCheckingTime;
        return false;
    }

    public boolean isSupersetPath(AttributeDependency path, ArrayList<AttributeDependency> prunedPaths) {
        long supersetPathCheckingTime = System.currentTimeMillis();
        boolean isPruned = false;
        for (AttributeDependency prunedPath : prunedPaths) {
            if (path.getRhs().equals(prunedPath.getRhs()) && path.getLhs().containsAll(prunedPath.getLhs())) {
//                System.out.println("Candidate path " + path + " is a superset of pruned path " + prunedPath);
                isPruned = true;
            }
        }
        supersetPathCheckingTime = System.currentTimeMillis()-supersetPathCheckingTime;
//        printWithTime("supersetPathCheckingTime", supersetPathCheckingTime);
//        totalSupersetPathCheckingTime += supersetPathCheckingTime;
        return isPruned;
    }

    public ArrayList<TGFD> deltaDiscovery(PatternTreeNode patternNode, LiteralTreeNode literalTreeNode, AttributeDependency literalPath, ArrayList<HashSet<ConstantLiteral>> matchesPerTimestamps) {
        ArrayList<TGFD> tgfds = new ArrayList<>();

        // Add dependency attributes to pattern
        // TO-DO: Fix - when multiple vertices in a pattern have the same type, attribute values get overwritten
        VF2PatternGraph patternForDependency = patternNode.getPattern().copy();
        Set<ConstantLiteral> attributesSetForDependency = new HashSet<>();
        attributesSetForDependency.addAll(literalPath.getLhs());
        attributesSetForDependency.add(literalPath.getRhs());
        for (Vertex v : patternForDependency.getPattern().vertexSet()) {
            String vType = new ArrayList<>(v.getTypes()).get(0);
            for (ConstantLiteral attribute : attributesSetForDependency) {
                if (vType.equals(attribute.getVertexType())) {
                    v.addAttribute(new Attribute(attribute.getAttrName()));
                }
            }
        }

        System.out.println("Pattern: " + patternForDependency);
        System.out.println("Dependency: " + "\n\tY=" + literalPath.getRhs() + ",\n\tX={" + literalPath.getLhs() + "\n\t}");

        System.out.println("Performing Entity Discovery");

        // Discover entities
        long findEntitiesTime = System.currentTimeMillis();
        Map<Set<ConstantLiteral>, ArrayList<Entry<ConstantLiteral, List<Integer>>>> entities = findEntities(literalPath, matchesPerTimestamps);
        findEntitiesTime = System.currentTimeMillis() - findEntitiesTime;
//        printWithTime("findEntitiesTime", findEntitiesTime);
//        totalFindEntitiesTime += findEntitiesTime;
        if (entities == null) {
            System.out.println("Mark as Pruned. No entities found during entity discovery.");
            if (!this.hasNoSupportPruning()) {
                literalTreeNode.setIsPruned();
                patternNode.addLowSupportDependency(literalPath);
            }
            return tgfds;
        }
        System.out.println("Number of entities discovered: " + entities.size());

        System.out.println("Discovering constant TGFDs");

        // Find Constant TGFDs
        Map<Pair,ArrayList<TreeSet<Pair>>> deltaToPairsMap = new HashMap<>();
        long discoverConstantTGFDsTime = System.currentTimeMillis();
        ArrayList<TGFD> constantTGFDs = discoverConstantTGFDs(patternNode, literalPath.getRhs(), entities, deltaToPairsMap);
        discoverConstantTGFDsTime = System.currentTimeMillis() - discoverConstantTGFDsTime;
//        printWithTime("discoverConstantTGFDsTime", discoverConstantTGFDsTime);
//        totalDiscoverConstantTGFDsTime += discoverConstantTGFDsTime;
        // TO-DO: Try discover general TGFD even if no constant TGFD candidate met support threshold
        System.out.println("Constant TGFDs discovered: " + constantTGFDs.size());
        tgfds.addAll(constantTGFDs);

        System.out.println("Discovering general TGFDs");

        // Find general TGFDs
        long discoverGeneralTGFDTime = System.currentTimeMillis();
        ArrayList<TGFD> generalTGFD;
        if(patternNode.getPatternSupport() == null){
            generalTGFD = discoverGeneralTGFD(patternNode, 0, literalPath, entities.size(), deltaToPairsMap);
        }else{
            generalTGFD = discoverGeneralTGFD(patternNode, patternNode.getPatternSupport(), literalPath, entities.size(), deltaToPairsMap);
        }
        discoverGeneralTGFDTime = System.currentTimeMillis() - discoverGeneralTGFDTime;
//        printWithTime("discoverGeneralTGFDTime", discoverGeneralTGFDTime);
//        totalDiscoverGeneralTGFDTime += discoverGeneralTGFDTime;
        if (generalTGFD.size() > 0) {
            System.out.println("Marking literal node as pruned. Discovered general TGFDs for this dependency.");
            if (!this.noMinimalityPruning) {
                literalTreeNode.setIsPruned();
                patternNode.addMinimalDependency(literalPath);
            }
        }
        tgfds.addAll(generalTGFD);

        return tgfds;
    }

    public static Map<Set<ConstantLiteral>, ArrayList<Entry<ConstantLiteral, List<Integer>>>> findEntities(AttributeDependency attributes, ArrayList<HashSet<ConstantLiteral>> matchesPerTimestamps) {
        String yVertexType = attributes.getRhs().getVertexType();
        String yAttrName = attributes.getRhs().getAttrName();
        Set<ConstantLiteral> xAttributes = attributes.getLhs();
        Map<Set<ConstantLiteral>, Map<ConstantLiteral, List<Integer>>> entitiesWithRHSvalues = new HashMap<>();
        int t = 2015;
//        for (ArrayList<HashSet<ConstantLiteral>> matchesInOneTimeStamp : matchesPerTimestamps) {
//            System.out.println("---------- Attribute values in " + t + " ---------- ");
        int numOfMatches = 0;
        if (matchesPerTimestamps.size() > 0) {
            for(HashSet<ConstantLiteral> match : matchesPerTimestamps) {
                if (match.size() < attributes.size()) continue;
                Set<ConstantLiteral> entity = new HashSet<>();
                ConstantLiteral rhs = null;
                for (ConstantLiteral literalInMatch : match) {
                    if (literalInMatch.getVertexType().equals(yVertexType) && literalInMatch.getAttrName().equals(yAttrName)) {
                        rhs = new ConstantLiteral(literalInMatch.getVertexType(), literalInMatch.getAttrName(), literalInMatch.getAttrValue());
                        continue;
                    }
                    for (ConstantLiteral attibute : xAttributes) {
                        if (literalInMatch.getVertexType().equals(attibute.getVertexType()) && literalInMatch.getAttrName().equals(attibute.getAttrName())) {
                            entity.add(new ConstantLiteral(literalInMatch.getVertexType(), literalInMatch.getAttrName(), literalInMatch.getAttrValue()));
                        }
                    }
                }
                if (entity.size() < xAttributes.size() || rhs == null) continue;
                if (!entitiesWithRHSvalues.containsKey(entity)) {
                    entitiesWithRHSvalues.put(entity, new HashMap<>());
                }
                if (!entitiesWithRHSvalues.get(entity).containsKey(rhs)) {
                    entitiesWithRHSvalues.get(entity).put(rhs, new ArrayList<>());
                }
                entitiesWithRHSvalues.get(entity).get(rhs).add(t);
                numOfMatches++;
            }
        }
        System.out.println("Number of matches: " + numOfMatches);
//            t++;
//        }
        if (entitiesWithRHSvalues.size() == 0) return null;

        Comparator<Entry<ConstantLiteral, List<Integer>>> comparator = new Comparator<Entry<ConstantLiteral, List<Integer>>>() {
            @Override
            public int compare(Entry<ConstantLiteral, List<Integer>> o1, Entry<ConstantLiteral, List<Integer>> o2) {
                return o2.getValue().size() - o1.getValue().size();
            }
        };

        Map<Set<ConstantLiteral>, ArrayList<Entry<ConstantLiteral, List<Integer>>>> entitiesWithSortedRHSvalues = new HashMap<>();
        for (Set<ConstantLiteral> entity : entitiesWithRHSvalues.keySet()) {
            Map<ConstantLiteral, List<Integer>> rhsMapOfEntity = entitiesWithRHSvalues.get(entity);
            ArrayList<Entry<ConstantLiteral, List<Integer>>> sortedRhsMapOfEntity = new ArrayList<>(rhsMapOfEntity.entrySet());
            sortedRhsMapOfEntity.sort(comparator);
            entitiesWithSortedRHSvalues.put(entity, sortedRhsMapOfEntity);
        }

        return entitiesWithSortedRHSvalues;
    }

//    public static Map<Set<ConstantLiteral>, ArrayList<Entry<ConstantLiteral, List<Integer>>>> findPartialEntities(AttributeDependency attributes, ArrayList<HashSet<ConstantLiteral>> partialMatchesPerTimestamps){
//        String rightVertexType = attributes.getRhs().getVertexType();
//        String rightVertexName = attributes.getRhs().getAttrName();
//        String rightVertexValue = attributes.getRhs().getAttrValue();
//        HashSet<ConstantLiteral> leftVertex = attributes.getLhs();
////        for(HashSet<ConstantLiteral> partialMatchInOneTimestamp : partialMatchesPerTimestamps){
////            partialMatchInOneTimestamp
////        }
//        if (matchesPerTimestamps.size() > 0) {
//            for(HashSet<ConstantLiteral> match : matchesPerTimestamps) {
//                if (match.size() < attributes.size()) continue;
//                Set<ConstantLiteral> entity = new HashSet<>();
//                ConstantLiteral rhs = null;
//                for (ConstantLiteral literalInMatch : match) {
//                    if (literalInMatch.getVertexType().equals(yVertexType) && literalInMatch.getAttrName().equals(yAttrName)) {
//                        rhs = new ConstantLiteral(literalInMatch.getVertexType(), literalInMatch.getAttrName(), literalInMatch.getAttrValue());
//                        continue;
//                    }
//                    for (ConstantLiteral attibute : xAttributes) {
//                        if (literalInMatch.getVertexType().equals(attibute.getVertexType()) && literalInMatch.getAttrName().equals(attibute.getAttrName())) {
//                            entity.add(new ConstantLiteral(literalInMatch.getVertexType(), literalInMatch.getAttrName(), literalInMatch.getAttrValue()));
//                        }
//                    }
//                }
//                if (!entitiesWithRHSvalues.containsKey(entity)) {
//                    entitiesWithRHSvalues.put(entity, new HashMap<>());
//                }
//                if (!entitiesWithRHSvalues.get(entity).containsKey(rhs)) {
//                    entitiesWithRHSvalues.get(entity).put(rhs, new ArrayList<>());
//                }
//                entitiesWithRHSvalues.get(entity).get(rhs).add(t);
//                numOfMatches++;
//            }
//        }
//        System.out.println("Number of matches: " + numOfMatches);
////            t++;
////        }
//        if (entitiesWithRHSvalues.size() == 0) return null;
//
//        Comparator<Entry<ConstantLiteral, List<Integer>>> comparator = new Comparator<Entry<ConstantLiteral, List<Integer>>>() {
//            @Override
//            public int compare(Entry<ConstantLiteral, List<Integer>> o1, Entry<ConstantLiteral, List<Integer>> o2) {
//                return o2.getValue().size() - o1.getValue().size();
//            }
//        };
//
//        Map<Set<ConstantLiteral>, ArrayList<Entry<ConstantLiteral, List<Integer>>>> entitiesWithSortedRHSvalues = new HashMap<>();
//        for (Set<ConstantLiteral> entity : entitiesWithRHSvalues.keySet()) {
//            Map<ConstantLiteral, List<Integer>> rhsMapOfEntity = entitiesWithRHSvalues.get(entity);
//            ArrayList<Entry<ConstantLiteral, List<Integer>>> sortedRhsMapOfEntity = new ArrayList<>(rhsMapOfEntity.entrySet());
//            sortedRhsMapOfEntity.sort(comparator);
//            entitiesWithSortedRHSvalues.put(entity, sortedRhsMapOfEntity);
//        }
//
//        return entitiesWithSortedRHSvalues;
//    }


    private ArrayList<TGFD> discoverConstantTGFDs(PatternTreeNode patternNode, ConstantLiteral yLiteral, Map<Set<ConstantLiteral>, ArrayList<Entry<ConstantLiteral, List<Integer>>>> entities, Map<Pair, ArrayList<TreeSet<Pair>>> deltaToPairsMap) {
        ArrayList<TGFD> tgfds = new ArrayList<>();
        String yVertexType = yLiteral.getVertexType();
        String yAttrName = yLiteral.getAttrName();
        for (Entry<Set<ConstantLiteral>, ArrayList<Entry<ConstantLiteral, List<Integer>>>> entityEntry : entities.entrySet()) {
            VF2PatternGraph newPattern = patternNode.getPattern().copy();
            Dependency newDependency = new Dependency();
            AttributeDependency constantPath = new AttributeDependency();
            for (Vertex v : newPattern.getPattern().vertexSet()) {
                String vType = new ArrayList<>(v.getTypes()).get(0);
                if (vType.equalsIgnoreCase(yVertexType)) { // TO-DO: What if our pattern has duplicate vertex types?
                    v.addAttribute(new Attribute(yAttrName));
                    if (newDependency.getY().size() == 0) {
                        VariableLiteral newY = new VariableLiteral(yVertexType, yAttrName, yVertexType, yAttrName);
                        newDependency.addLiteralToY(newY);
                    }
                }
                for (ConstantLiteral xLiteral : entityEntry.getKey()) {
                    if (xLiteral.getVertexType().equalsIgnoreCase(vType)) {
                        v.addAttribute(new Attribute(xLiteral.getAttrName(), xLiteral.getAttrValue()));
                        ConstantLiteral newXLiteral = new ConstantLiteral(vType, xLiteral.getAttrName(), xLiteral.getAttrValue());
                        newDependency.addLiteralToX(newXLiteral);
                        constantPath.addToLhs(newXLiteral);
                    }
                }
            }
            constantPath.setRhs(new ConstantLiteral(yVertexType, yAttrName, null));

            System.out.println("Performing Constant TGFD discovery");
            System.out.println("Pattern: " + newPattern);
            System.out.println("Entity: " + newDependency);

            System.out.println("Candidate RHS values for entity...");
            ArrayList<Entry<ConstantLiteral, List<Integer>>> attrValuesTimestampsSortedByFreq = entityEntry.getValue();
            for (Entry<ConstantLiteral, List<Integer>> entry : attrValuesTimestampsSortedByFreq) {
                System.out.println(entry.getKey() + ":" + entry.getValue());
            }

            System.out.println("Computing candidate delta for RHS value...\n" + attrValuesTimestampsSortedByFreq.get(0).getKey());
            ArrayList<Pair> candidateDeltas = new ArrayList<>();
            if (attrValuesTimestampsSortedByFreq.size() == 1) {
                List<Integer> timestamps = attrValuesTimestampsSortedByFreq.get(0).getValue();
                int minDistance = this.numOfSnapshots - 1;
                int maxDistance = timestamps.get(timestamps.size() - 1) - timestamps.get(0);
                for (int index = 1; index < timestamps.size(); index++) {
                    minDistance = Math.min(minDistance, timestamps.get(index) - timestamps.get(index - 1));
                }
                if (minDistance > maxDistance) {
                    System.out.println("Not enough timestamped matches found for entity.");
                    continue;
                }
                candidateDeltas.add(new Pair(minDistance, maxDistance));
            } else if (attrValuesTimestampsSortedByFreq.size() > 1) {
                List<Integer> mostFreqTimestamps = attrValuesTimestampsSortedByFreq.get(0).getValue();
                int minExclusionDistance = this.numOfSnapshots - 1;
                int maxExclusionDistance = 0;
                for (Entry<ConstantLiteral, List<Integer>> otherTimestamps : attrValuesTimestampsSortedByFreq.subList(1,attrValuesTimestampsSortedByFreq.size())) {
                    for (Integer timestamp: otherTimestamps.getValue()) {
                        for (Integer refTimestamp: mostFreqTimestamps) {
                            int distance = Math.abs(timestamp - refTimestamp);
                            minExclusionDistance = Math.min(minExclusionDistance, distance);
                            maxExclusionDistance = Math.max(maxExclusionDistance, distance);
                        }
                    }
                    if (minExclusionDistance == 0 && maxExclusionDistance == (this.numOfSnapshots-1)) break;
                }
                if (minExclusionDistance > 0) {
                    candidateDeltas.add(new Pair(0, minExclusionDistance-1));
                }
                if (maxExclusionDistance < this.numOfSnapshots-1) {
                    candidateDeltas.add(new Pair(maxExclusionDistance+1, this.numOfSnapshots-1));
                }
            }
            if (candidateDeltas.size() == 0) {
                System.out.println("Could not find any deltas for entity: " + entityEntry.getKey());
                continue;
            }

            // Compute TGFD support
            Delta candidateTGFDdelta;
            double candidateTGFDsupport = 0;
            Pair mostSupportedDelta = null;
            TreeSet<Pair> mostSupportedSatisfyingPairs = null;
            double denominator = 2 * entities.size() * this.numOfSnapshots;
            for (Pair candidateDelta : candidateDeltas) {
                int minDistance = candidateDelta.min();
                int maxDistance = candidateDelta.max();
                if (minDistance <= maxDistance) {
                    System.out.println("Calculating support for candidate delta ("+minDistance+","+maxDistance+")");
                    double numerator;
                    List<Integer> timestamps = attrValuesTimestampsSortedByFreq.get(0).getValue();
                    TreeSet<Pair> satisfyingPairs = new TreeSet<>();
                    for (int index = 0; index < timestamps.size() - 1; index++) {
                        for (int j = index + 1; j < timestamps.size(); j++) {
                            if (timestamps.get(j) - timestamps.get(index) >= minDistance && timestamps.get(j) - timestamps.get(index) <= maxDistance) {
                                satisfyingPairs.add(new Pair(timestamps.get(index), timestamps.get(j)));
                            }
                        }
                    }

                    System.out.println("Satisfying pairs: " + satisfyingPairs);

                    numerator = satisfyingPairs.size();
                    double candidateSupport = numerator / denominator;

                    if (candidateSupport > candidateTGFDsupport) {
                        candidateTGFDsupport = candidateSupport;
                        mostSupportedDelta = candidateDelta;
                        mostSupportedSatisfyingPairs = satisfyingPairs;
                    }
                }
            }
            if (mostSupportedDelta == null) {
                System.out.println("Could not come up with mostSupportedDelta for entity: " + entityEntry.getKey());
                continue;
            }
            System.out.println("Entity satisfying attributes:" + mostSupportedSatisfyingPairs);
            System.out.println("Entity delta = " + mostSupportedDelta);
            System.out.println("Entity support : "+mostSupportedSatisfyingPairs.size()+"/"+denominator+" = " + candidateTGFDsupport);

            // All entities are considered in general TGFD, regardless of their support
            if (!deltaToPairsMap.containsKey(mostSupportedDelta)) {
                deltaToPairsMap.put(mostSupportedDelta, new ArrayList<>());
            }
            deltaToPairsMap.get(mostSupportedDelta).add(mostSupportedSatisfyingPairs);

            this.constantTgfdSupportsList.add(candidateTGFDsupport); // Statistics

            // Only output constant TGFDs that satisfy support
            if (candidateTGFDsupport < this.getTheta()) {
                System.out.println("Could not satisfy TGFD support threshold for entity: " + entityEntry.getKey());
                continue;
            }
            int minDistance = mostSupportedDelta.min();
            int maxDistance = mostSupportedDelta.max();
            candidateTGFDdelta = new Delta(Period.ofDays(minDistance * 183), Period.ofDays(maxDistance * 183 + 1), Duration.ofDays(183));
            System.out.println("Constant TGFD delta: "+candidateTGFDdelta);

            if (!this.noMinimalityPruning && isSupersetPath(constantPath, patternNode.getAllMinimalConstantDependenciesOnThisPath())) { // Ensures we don't expand constant TGFDs from previous iterations
                System.out.println("Candidate constant TGFD " + constantPath + " is a superset of an existing minimal constant TGFD");
                continue;
            }
            System.out.println("Creating new constant TGFD...");
            TGFD entityTGFD = new TGFD(newPattern, candidateTGFDdelta, newDependency, candidateTGFDsupport, patternNode.getPatternSupport(), "");
            System.out.println("TGFD: " + entityTGFD);
            tgfds.add(entityTGFD);
            if (!this.noMinimalityPruning) patternNode.addMinimalConstantDependency(constantPath);
        }
        return tgfds;
    }

    private ArrayList<TGFD> discoverGeneralTGFD(PatternTreeNode patternTreeNode, double patternSupport, AttributeDependency literalPath, int entitiesSize, Map<Pair, ArrayList<TreeSet<Pair>>> deltaToPairsMap) {

        ArrayList<TGFD> tgfds = new ArrayList<>();

        System.out.println("Number of delta: " + deltaToPairsMap.keySet().size());
        for (Pair deltaPair : deltaToPairsMap.keySet()) {
            System.out.println("constant delta: " + deltaPair);
        }

        System.out.println("Delta to Pairs map...");
        int numOfEntitiesWithDeltas = 0;
        int numOfPairs = 0;
        for (Entry<Pair, ArrayList<TreeSet<Pair>>> deltaToPairsEntry : deltaToPairsMap.entrySet()) {
            numOfEntitiesWithDeltas += deltaToPairsEntry.getValue().size();
            for (TreeSet<Pair> pairSet : deltaToPairsEntry.getValue()) {
                System.out.println(deltaToPairsEntry.getKey()+":"+pairSet);
                numOfPairs += pairSet.size();
            }
        }
        System.out.println("Number of entities with deltas: " + numOfEntitiesWithDeltas);
        System.out.println("Number of pairs: " + numOfPairs);


        // Find intersection delta
        HashMap<Pair, ArrayList<Pair>> intersections = new HashMap<>();
        int currMin = 0;
        int currMax = this.numOfSnapshots - 1;
        // TO-DO: Verify if TreeSet<Pair> is being sorted correctly
        // TO-DO: Does this method only produce intervals (x,y), where x == y ?
        ArrayList<Pair> currSatisfyingAttrValues = new ArrayList<>();
        for (Pair deltaPair: deltaToPairsMap.keySet()) {
            if (Math.max(currMin, deltaPair.min()) <= Math.min(currMax, deltaPair.max())) {
                currMin = Math.max(currMin, deltaPair.min());
                currMax = Math.min(currMax, deltaPair.max());
//				currSatisfyingAttrValues.add(satisfyingPairsSet.get(index)); // By axiom 4
                continue;
            }
            for (Entry<Pair, ArrayList<TreeSet<Pair>>> deltaToPairsEntry : deltaToPairsMap.entrySet()) {
                for (TreeSet<Pair> satisfyingPairSet : deltaToPairsEntry.getValue()) {
                    for (Pair satisfyingPair : satisfyingPairSet) {
                        if (satisfyingPair.max() - satisfyingPair.min() >= currMin && satisfyingPair.max() - satisfyingPair.min() <= currMax) {
                            currSatisfyingAttrValues.add(new Pair(satisfyingPair.min(), satisfyingPair.max()));
                        }
                    }
                }
            }
            intersections.putIfAbsent(new Pair(currMin, currMax), currSatisfyingAttrValues);
            currSatisfyingAttrValues = new ArrayList<>();
            currMin = 0;
            currMax = this.numOfSnapshots - 1;
            if (Math.max(currMin, deltaPair.min()) <= Math.min(currMax, deltaPair.max())) {
                currMin = Math.max(currMin, deltaPair.min());
                currMax = Math.min(currMax, deltaPair.max());
//				currSatisfyingAttrValues.add(satisfyingPairsSet.get(index));
            }
        }
        for (Entry<Pair, ArrayList<TreeSet<Pair>>> deltaToPairsEntry : deltaToPairsMap.entrySet()) {
            for (TreeSet<Pair> satisfyingPairSet : deltaToPairsEntry.getValue()) {
                for (Pair satisfyingPair : satisfyingPairSet) {
                    if (satisfyingPair.max() - satisfyingPair.min() >= currMin && satisfyingPair.max() - satisfyingPair.min() <= currMax) {
                        currSatisfyingAttrValues.add(new Pair(satisfyingPair.min(), satisfyingPair.max()));
                    }
                }
            }
        }
        intersections.putIfAbsent(new Pair(currMin, currMax), currSatisfyingAttrValues);

        ArrayList<Entry<Pair, ArrayList<Pair>>> sortedIntersections = new ArrayList<>(intersections.entrySet());
        sortedIntersections.sort(new Comparator<Entry<Pair, ArrayList<Pair>>>() {
            @Override
            public int compare(Entry<Pair, ArrayList<Pair>> o1, Entry<Pair, ArrayList<Pair>> o2) {
                return o2.getValue().size() - o1.getValue().size();
            }
        });

        System.out.println("Candidate deltas for general TGFD:");
        for (Entry<Pair, ArrayList<Pair>> intersection : sortedIntersections) {
            System.out.println(intersection.getKey());
        }

        System.out.println("Evaluating candidate deltas for general TGFD...");
        for (Entry<Pair, ArrayList<Pair>> intersection : sortedIntersections) {
            Pair candidateDelta = intersection.getKey();
//			if (!this.noSupportPruning && isSupersetPath(literalPath, candidateDelta, patternTreeNode.getAllLowSupportGeneralTgfds())) {
//				continue;
//			}
            int generalMin = candidateDelta.min();
            int generalMax = candidateDelta.max();
            System.out.println("Calculating support for candidate general TGFD candidate delta: " + intersection.getKey());

            // Compute general support
            double denominator = 2 * entitiesSize * this.numOfSnapshots;

            int numberOfSatisfyingPairs = intersection.getValue().size();

            System.out.println("Number of satisfying pairs: " + numberOfSatisfyingPairs);
            System.out.println("Satisfying pairs: " + intersection.getValue());

            double support = numberOfSatisfyingPairs / denominator;
            System.out.println("Candidate general TGFD support = " + numberOfSatisfyingPairs + "/" + denominator);
            System.out.println("Candidate general TGFD support: " + support);
            this.generalTgfdSupportsList.add(support);
            if (support < this.getTheta()) {
//				if (!this.noSupportPruning) patternTreeNode.addLowSupportDependency(literalPath);
                System.out.println("Support for candidate general TGFD is below support threshold");
                continue;
            }

            System.out.println("TGFD Support = " + numberOfSatisfyingPairs + "/" + denominator);

            Delta delta = new Delta(Period.ofDays(generalMin * 183), Period.ofDays(generalMax * 183 + 1), Duration.ofDays(183));

            Dependency generalDependency = new Dependency();
            String yVertexType = literalPath.getRhs().getVertexType();
            String yAttrName = literalPath.getRhs().getAttrName();
            VariableLiteral y = new VariableLiteral(yVertexType, yAttrName, yVertexType, yAttrName);
            generalDependency.addLiteralToY(y);
            for (ConstantLiteral x : literalPath.getLhs()) {
                String xVertexType = x.getVertexType();
                String xAttrName = x.getAttrName();
                VariableLiteral varX = new VariableLiteral(xVertexType, xAttrName, xVertexType, xAttrName);
                generalDependency.addLiteralToX(varX);
            }

            System.out.println("Creating new general TGFD...");
            TGFD tgfd = new TGFD(patternTreeNode.getPattern(), delta, generalDependency, support, patternSupport, "");
            System.out.println("TGFD: " + tgfd);
            tgfds.add(tgfd);
        }
        return tgfds;
    }

    public ArrayList<ArrayList<TGFD>> getTgfds() {
        return tgfds;
    }

    public double getTheta() {
        return theta;
    }

    public static class Pair implements Comparable<Pair> {
        private final Integer min;
        private final Integer max;

        public Pair(int min, int max) {
            this.min = min;
            this.max = max;
        }

        public Integer min() {
            return min;
        }

        public Integer max() {
            return max;
        }

        @Override
        public int compareTo(@NotNull TestPattern.Pair o) {
            if (this.min.equals(o.min)) {
                return this.max.compareTo(o.max);
            } else {
                return this.min.compareTo(o.min);
            }
        }

        @Override
        public String toString() {
            return "(" + min +
                    ", " + max +
                    ')';
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Pair pair = (Pair) o;
            return min.equals(pair.min) && max.equals(pair.max);
        }

        @Override
        public int hashCode() {
            return Objects.hash(min, max);
        }
    }

    public static void main(String[] args) throws IOException {
        TestPattern testPattern = new TestPattern();
        GraphLoader graph = testPattern.loadGraph();
        testPattern.loadPartition();
        testPattern.histogram(graph);
        testPattern.initialize(graph);
        long totalvSpawn = 0;
        long totalMatch = 0;
        long totalhSpawn = 0;
        while(testPattern.getCurrentVSpawnLevel() <= testPattern.getK()){
            System.out.println("VSpawn level " + testPattern.getCurrentVSpawnLevel());
//            System.out.println("Previous level node index " + testPattern.getPreviousLevelNodeIndex());
//            System.out.println("Candidate edge index " + testPattern.getCandidateEdgeIndex());

            PatternTreeNode patternTreeNode = null;
            long vSpawnTime = System.currentTimeMillis();
            while (patternTreeNode == null && testPattern.getCurrentVSpawnLevel() <= testPattern.getK()) {
                patternTreeNode = testPattern.vSpawn();
            }
            vSpawnTime = System.currentTimeMillis()-vSpawnTime;

            assert patternTreeNode != null;
            System.out.println("Pattern is "+patternTreeNode.toString());
            System.out.println("vSpawnTime"+vSpawnTime);
            totalvSpawn += vSpawnTime;
            System.out.println("Total v"+totalvSpawn);

            if (testPattern.getCurrentVSpawnLevel() > testPattern.getK()) break;

            long matchingTime = System.currentTimeMillis();
            ArrayList<HashSet<ConstantLiteral>> matches = new ArrayList<>();
            testPattern.findMatchesUsingCenterVertices(graph, patternTreeNode, matches);
            matchingTime = System.currentTimeMillis() - matchingTime;
            System.out.println("matchingTime"+matchingTime);
            totalMatch += matchingTime;
            System.out.println("Total m"+totalMatch);

            if (testPattern.isSkipK1() && testPattern.getCurrentVSpawnLevel() == 1) continue;

            long hSpawnTime = System.currentTimeMillis();
            ArrayList<TGFD> tgfds = testPattern.hSpawn(patternTreeNode, matches);
            hSpawnTime = System.currentTimeMillis() - hSpawnTime;
            System.out.println("hSpwanTime"+hSpawnTime);
            totalhSpawn += hSpawnTime;
            System.out.println("Total h"+totalhSpawn);

            for(TGFD tgfd:tgfds){
                System.out.println("TGFD is " + tgfd.toString());
            }
            testPattern.getTgfds().get(testPattern.getCurrentVSpawnLevel()).addAll(tgfds);
        }
        System.out.println(testPattern.getTgfds().get(1).size());
        System.out.println(testPattern.getTgfds().get(2).size());
        System.out.println(testPattern.getTgfds().get(3).size());
    }
}
