import graphLoader.DBPediaLoader;
import Infra.*;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.Array;
import java.io.File;
import java.util.*;

public class testPartition {
    public testPartition() {
    }

    public static void main(String []args){
        String prefix = "/home/ubuntu/";
        DBPediaLoader dbpedia2015 = new DBPediaLoader(new ArrayList<>(), new ArrayList<>(Collections.singletonList(prefix+"2015/2015types.ttl")), new ArrayList<>(Arrays.asList(prefix+"2015/2015literals.ttl", prefix+"2015/2015objects.ttl")));
//        DBPediaLoader dbpedia2016 = new DBPediaLoader(new ArrayList<>(), new ArrayList<>(Collections.singletonList(prefix+"2016/2016types.ttl")), new ArrayList<>(Arrays.asList(prefix+"2016/2016literals.ttl", prefix+"2016/2016objects.ttl")));
//        DBPediaLoader dbpedia2017 = new DBPediaLoader(new ArrayList<>(), new ArrayList<>(Collections.singletonList(prefix+"2017/2017types.ttl")), new ArrayList<>(Arrays.asList(prefix+"2017/2017literals.ttl", prefix+"2017/2017objects.ttl")));
//        ArrayList<DBPediaLoader> loaders = new ArrayList<>(Arrays.asList(dbpedia2015,dbpedia2016,dbpedia2017));
//
//        //TODO: Get number of vertexType
//        HashSet<String> vertexTypes = new HashSet<>();
//        for(DBPediaLoader loader : loaders){
//            for(Vertex vertex : loader.getGraph().getGraph().vertexSet()){
//                vertexTypes.addAll(vertex.getTypes());
//            }
//        }
//        System.out.println("Number of vertexType is "+vertexTypes.size());
//
//        //TODO: Check what the most popular edgeType is and number of edgeType
//        HashMap<String, Integer> edgeTypesHistogram = new HashMap<>();
//        HashSet<String> edgeTypes = new HashSet<>();
//        for(DBPediaLoader loader : loaders){
//            for(RelationshipEdge edge : loader.getGraph().getGraph().edgeSet()){
//                Vertex source = edge.getSource();
//                Vertex target = edge.getTarget();
//                String label = edge.getLabel();
//                for(String sourceType : source.getTypes()){
//                    for(String targetType : target.getTypes()){
//                        String edgeType = sourceType + "+" + label + "+" + targetType;
//                        edgeTypes.add(edgeType);
//                        edgeTypesHistogram.merge(edgeType,1,Integer::sum);
//                    }
//                }
//            }
//        }
//        System.out.println("Number of edgeTypes is "+edgeTypes.size());
//        ArrayList<Map.Entry<String, Integer>> sortedEdgesHist = new ArrayList<>(edgeTypesHistogram.entrySet());
//        sortedEdgesHist.sort((o1, o2) -> o2.getValue() - o1.getValue());
//        for (Map.Entry<String, Integer> entry : sortedEdgesHist) {
//            String edgeTypeName = entry.getKey();
//            Integer edgeTypeFrequency = entry.getValue();
//            System.out.println(edgeTypeName + " " + edgeTypeFrequency);
//            break;
//        }

        //TODO: get all vertex and frequency
        HashSet<String> restVertexTypes = new HashSet<>();
        HashMap<String, Integer> vertexTypesHistogram = new HashMap<>();
        for(Vertex vertex : dbpedia2015.getGraph().getGraph().vertexSet()){
            restVertexTypes.addAll(vertex.getTypes());
            for(String vertexType : vertex.getTypes()){
                vertexTypesHistogram.merge(vertexType,1,Integer::sum);
            }
        }
        int numOfVertexType = restVertexTypes.size();
        System.out.println("Finished first step");
        //TODO: get all edges and weight and neighbour and workload
        int totalWorkload = 0;
        HashSet<String> restEdgeTypes = new HashSet<>();
        HashMap<String, Integer> edgeTypesHistogram = new HashMap<>();
        HashMap<String, ArrayList<String>> neighbourMap = new HashMap<>();
        for(RelationshipEdge edge : dbpedia2015.getGraph().getGraph().edgeSet()){
            Vertex source = edge.getSource();
            Vertex target = edge.getTarget();
//            String label = edge.getLabel();
            for(String sourceType : source.getTypes()){
                for(String targetType : target.getTypes()){
                    String edgeType = sourceType + "-" + targetType;
                    totalWorkload++;
                    restEdgeTypes.add(edgeType);
                    edgeTypesHistogram.merge(edgeType,1,Integer::sum);
                    if(!neighbourMap.containsKey(sourceType)) neighbourMap.put(sourceType,new ArrayList<>());
                    neighbourMap.get(sourceType).add(targetType);
                    if(!neighbourMap.containsKey(targetType)) neighbourMap.put(targetType,new ArrayList<>());
                    neighbourMap.get(targetType).add(sourceType);
                }
            }
        }
        System.out.println("Finished second step");
        //TODO: init object and all helper data
        testPartition tp = new testPartition();
        tp.restVertexTypes = restVertexTypes;
        tp.vertexTypesHistogram = vertexTypesHistogram;
        tp.restEdgeTypes = restEdgeTypes;
        tp.edgeTypesHistogram = edgeTypesHistogram;

        tp.machineNum = 4;
        tp.LIMIT = totalWorkload / tp.machineNum;
        tp.neighbourMap = neighbourMap;
        tp.workLoadOfMachine = new int[tp.machineNum];
        tp.edgeOnMachine = new int[tp.machineNum];
        tp.edgeTypeOnMachine = new ArrayList<>();
        tp.candidatesFrequencyMap = new ArrayList<>();
        tp.machineOwnSet = new ArrayList<>();
        tp.missingEdges = new HashSet<>();
        tp.missingEdgeType = new HashMap<>();
        for(int i=0;i<tp.machineNum;i++){
            tp.edgeTypeOnMachine.add(new HashMap<>());
            tp.candidatesFrequencyMap.add(new HashMap<>());
            tp.machineOwnSet.add(new HashSet<>());
        }
        //TODO: global logic
        int count = 0;
        while(!restVertexTypes.isEmpty()){
            for(int i=0;i<tp.machineNum;i++){
                if(!restVertexTypes.isEmpty() && tp.LIMIT > tp.workLoadOfMachine[i]){
                    tp.assignToMachine_nbn(i);
                    count++;
                    System.out.println("Finished assignment of "+count+"/"+numOfVertexType+" vertexType on machine" + i);
                }
            }
        }

        //TODO: show assignment on each machine
        int rest=0;
        for(int i=0;i<tp.machineNum;i++){
            System.out.println("WorkLoad on machine "+ i+ " is " + tp.workLoadOfMachine[i] + " and EdgeNum is " + tp.edgeOnMachine[i]);
//            rest += tp.workLoadOfMachine[i];
//            StringBuilder sb = new StringBuilder();
//            int cnt = 0;
//            for(String v:tp.machineOwnSet.get(i)){
//                sb.append(v).append(" ");
//                cnt++;
//            }
//            System.out.println(cnt+"["+sb+"]");
            try {//file create
                File myObj = new File("/home/ubuntu/machine-"+i+".txt");
                if (myObj.createNewFile()) {
                    System.out.println("File created: " + myObj.getName());
                } else {
                    System.out.println("File already exists.");
                }
            } catch (IOException e) {
                System.out.println("An error occurred.");
                e.printStackTrace();
            }
            try {//file write
                FileWriter myWriter = new FileWriter("/home/ubuntu/machine-"+i+".txt");
                for(String v:tp.machineOwnSet.get(i)){
                    myWriter.write(v+" ");
                }
                myWriter.close();
                System.out.println("Successfully wrote to the file.");
            } catch (IOException e) {
                System.out.println("An error occurred.");
                e.printStackTrace();
            }
        }
        System.out.println();

        //TODO: show information of missing edges
//        for(String e : tp.restEdgeTypes){
//            tp.missingEdgeType.put(e,edgeTypesHistogram.get(e));
//            String source=e.split("-")[0];
//            String destination=e.split("-")[1];
//            int weight= edgeTypesHistogram.get(e);
//            int sourcePlace=-1;
//            int destinationPlace=-1;
//            for(int i=0;i<tp.machineNum;i++){
//                if(tp.machineOwnSet.get(i).contains(source)) sourcePlace=i;
//                if(tp.machineOwnSet.get(i).contains(destination)) destinationPlace=i;
//            }
//            String missingEdge = source + " on machine " + sourcePlace + " and " + destination + " on machine " + destinationPlace + " weight is " + weight;
////            String missingEdge_reverse = destination + " on machine " + destinationPlace + " and " + source + " on machine " + sourcePlace + " weight is " + weight;
////            if(!tp.missingEdges.contains(missingEdge_reverse))
//            tp.missingEdges.add(missingEdge);
//
//        }
//        System.out.println("Info of Missing Edges: Totally " + tp.missingEdges.size() + " edges, " + "Sum of cut edges' weight is "+(totalWorkload-rest)+
//                " Total edges is " +totalWorkload+" Missing rate is "+(float)(totalWorkload-rest)/(totalWorkload));
////        for(String s:tp.missingEdges){
////            System.out.println(s);
////        }
        //TODO: merge all statistics on machines and missing
//        int frequentSetSize = 50;
//        HashMap<String,Integer> allEdgeTypeHist = new HashMap<>();
//        for(int i=0;i< tp.machineNum;i++){
//            allEdgeTypeHist.putAll(tp.edgeTypeOnMachine.get(i));
//        }
//        allEdgeTypeHist.putAll(tp.missingEdgeType);
//        ArrayList<Map.Entry<String, Integer>> sortedEdgesHist = new ArrayList<>(allEdgeTypeHist.entrySet());
//        sortedEdgesHist.sort((o1, o2) -> o2.getValue() - o1.getValue());
//        List<Map.Entry<String, Integer>> popularEdgeType = sortedEdgesHist.subList(0, Math.min(sortedEdgesHist.size(), frequentSetSize));
//        for(Map.Entry<String,Integer> entry: popularEdgeType){
//            System.out.println(entry.getKey() + " " + entry.getValue());
//        }
//        //TODO: naive way
//        int count1 = 0;
//        while(!restVertexTypes.isEmpty()){
//            for(int i=0;i<tp.machineNum;i++){
//                if(!restVertexTypes.isEmpty()){
//                    tp.assignToMachine_avg(i);
//                    count1++;
//                    System.out.println("Finished assignment of "+count1+"/"+numOfVertexType+" vertexType on machine" + i);
//                }
//            }
//        }
//        for(int i=0;i<tp.machineNum;i++){
//            System.out.println("WorkLoad on machine "+ i+ " is " + tp.workLoadOfMachine[i] + " and EdgeNum is " + tp.edgeOnMachine[i]);
//            StringBuilder sb = new StringBuilder();
//            int cnt = 0;
//            for(String v:tp.machineOwnSet.get(i)){
//                sb.append(v).append(" ");
//                cnt++;
//            }
//            System.out.println(cnt+"["+sb+"]");
//        }
//        System.out.println();
//
//        int missingWeight = 0;
//        for(String e : tp.restEdgeTypes){
//            String source=e.split("-")[0];
//            String destination=e.split("-")[1];
//            int weight= edgeTypesHistogram.get(e);
//            int sourcePlace=-1;
//            int destinationPlace=-1;
//            for(int i=0;i<tp.machineNum;i++){
//                if(tp.machineOwnSet.get(i).contains(source)) sourcePlace=i;
//                if(tp.machineOwnSet.get(i).contains(destination)) destinationPlace=i;
//            }
//            if(sourcePlace != destinationPlace) {
//                String missingEdge = source + " on machine " + sourcePlace + " and " + destination + " on machine " + destinationPlace + " weight is " + weight;
//                tp.missingEdges.add(missingEdge);
//                missingWeight += weight;
//            }
//
//        }
//        System.out.println("Info of Missing Edges: Totally " + tp.missingEdges.size() + " edges, " + "Sum of cut edges' weight is "+missingWeight+
//                " Total edges is " +totalWorkload+" Missing rate is "+(float)(missingWeight/totalWorkload));
//        for(String s:tp.missingEdges){
//            System.out.println(s);
//        }

    }

    public HashSet<String> restVertexTypes;
    public HashMap<String, Integer> vertexTypesHistogram;
    public HashSet<String> restEdgeTypes;
    public HashMap<String, Integer> edgeTypesHistogram;

    public int machineNum;
    public int LIMIT;
    public HashMap<String, ArrayList<String>> neighbourMap;
    public int[] workLoadOfMachine;
    public int[] edgeOnMachine;
    public ArrayList<HashMap<String,Integer>> edgeTypeOnMachine;
    public ArrayList<HashMap<String,Integer>> candidatesFrequencyMap;
    public ArrayList<HashSet<String>> machineOwnSet;
    public HashSet<String> missingEdges;
    public HashMap<String,Integer> missingEdgeType;

    public void assignToMachine_avg(int machine){
        String selected = null;
        for(String vertex : restVertexTypes)
        {
            selected = vertex;
            break;
        }
        vertexTypesHistogram.remove(selected);
        restVertexTypes.remove(selected);

        machineOwnSet.get(machine).add(selected);

        ArrayList<String> neighbours = neighbourMap.get(selected);
        if(neighbours == null || neighbours.isEmpty()){
            return;
        }
        for(String neighbour : neighbours){
            if(machineOwnSet.get(machine).contains(neighbour)){
                String edge = selected + "-" + neighbour;
                String edge_reverse = neighbour + "-" + selected;
                for(String e : restEdgeTypes){
                    if(e.equals(edge) || e.equals(edge_reverse)){
                        workLoadOfMachine[machine] += edgeTypesHistogram.get(e);
                        edgeOnMachine[machine] += 1;
                        restEdgeTypes.remove(e);
                        break;
                    }
                }
            }
        }

    }
    public void assignToMachine_nbn(int machine){
        HashMap<String,Integer> candidates = candidatesFrequencyMap.get(machine);
        if(candidates.isEmpty()){
            selectVertexFromHistogram(machine);
            return;
        }
        int maxFrequency = 0;
        String maxFrequencyVertex = null;
        for(String v : candidates.keySet()){
            if(restVertexTypes.contains(v)){
                if(candidates.get(v)>maxFrequency){
                    maxFrequency = candidates.get(v);
                    maxFrequencyVertex = v;
                }
            }
        }
        if(maxFrequencyVertex == null){
            selectVertexFromHistogram(machine);
        }else{
            selectVertexFromCandidates(machine,maxFrequencyVertex);
        }
    }

    public void selectVertexFromHistogram(int machine){
        String selected = null;
        int item = new Random().nextInt(restVertexTypes.size());
        int i = 0;
        for(String vertex : restVertexTypes)
        {
            if (i == item){
                selected = vertex;
                break;
            }
            i++;
        }
        vertexTypesHistogram.remove(selected);
        restVertexTypes.remove(selected);

        machineOwnSet.get(machine).add(selected);

        ArrayList<String> neighbours = neighbourMap.get(selected);
        if(neighbours == null || neighbours.isEmpty()){
            return;
        }
        HashMap<String,Integer> candidates = candidatesFrequencyMap.get(machine);
        for(String neighbour : neighbours){
            candidates.put(neighbour,candidates.getOrDefault(neighbour,0)+1);
        }
    }

    public void selectVertexFromCandidates(int machine, String maxFrequencyVertex){
        HashMap<String,Integer> candidates = candidatesFrequencyMap.get(machine);
        restVertexTypes.remove(maxFrequencyVertex);
        vertexTypesHistogram.remove(maxFrequencyVertex);
        candidates.remove(maxFrequencyVertex);

        machineOwnSet.get(machine).add(maxFrequencyVertex);

        ArrayList<String> neighbours = neighbourMap.get(maxFrequencyVertex);
        for(String neighbour : neighbours){
            if(machineOwnSet.get(machine).contains(neighbour)){
                String edge = maxFrequencyVertex + "-" + neighbour;
                String edge_reverse = neighbour + "-" + maxFrequencyVertex;
                for(String e : restEdgeTypes){
                    if(e.equals(edge) || e.equals(edge_reverse)){
                        workLoadOfMachine[machine] += edgeTypesHistogram.get(e);
                        edgeOnMachine[machine] += 1;
                        edgeTypeOnMachine.get(machine).put(e,edgeTypesHistogram.get(e));
                        restEdgeTypes.remove(e);
                        break;
                    }
                }
            }else{
                candidates.put(neighbour,candidates.getOrDefault(neighbour,0)+1);
            }
        }
    }
}














