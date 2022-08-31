package TgfdDiscovery;

import IncrementalRunner.IncUpdates;
import Infra.ConstantLiteral;
import Infra.PatternTreeNode;
import Infra.TGFD;
import changeExploration.Change;
import changeExploration.ChangeLoader;
import graphLoader.GraphLoader;
import org.json.simple.JSONArray;
import org.json.simple.parser.JSONParser;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.PrintStream;
import java.time.ZoneId;
import java.time.ZonedDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

public class TestChangeFile {
    public static void main(String[] args) {
        String overallTimeAndDateStamp = ZonedDateTime.now(ZoneId.systemDefault()).format(DateTimeFormatter.ofPattern("uuuu.MM.dd.HH.mm.ss"));
        ArrayList<Long> runtimes = new ArrayList<>();
        for (int index = 0; index < 4; index++) {

            TgfdDiscovery tgfdDiscovery = new TgfdDiscovery(args);

            tgfdDiscovery.setUseChangeFile(false);
            tgfdDiscovery.setReUseMatches(false);
            tgfdDiscovery.setValidationSearch(false);
            if (index == 0) {
                tgfdDiscovery.setUseChangeFile(true);
            } else if (index == 1) {
                tgfdDiscovery.setUseChangeFile(true);
                tgfdDiscovery.setReUseMatches(true);
            } else if (index == 2) {
                tgfdDiscovery.setReUseMatches(true);
            }

            List<GraphLoader> graphs;
            if (!tgfdDiscovery.isUseChangeFile()) {
                tgfdDiscovery.setUseChangeFile(true);
                graphs = tgfdDiscovery.loadDBpediaSnapshotsFromPath(tgfdDiscovery.getPath());
                tgfdDiscovery.setUseChangeFile(false);
            } else {
                graphs = tgfdDiscovery.loadDBpediaSnapshotsFromPath(tgfdDiscovery.getPath());
            }

            // Had to compute histogram using only first snapshot because we need dummy TGFDs to build the other graphs
            // TO-DO: Is there a better way?
            final long histogramTime = System.currentTimeMillis();
            if (tgfdDiscovery.isUseChangeFile()) {
                tgfdDiscovery.histogram(tgfdDiscovery.getTimestampToFilesMap().subList(0,1));
            } else {
                tgfdDiscovery.histogram(graphs);
            }
            TgfdDiscovery.printWithTime("histogramTime", (System.currentTimeMillis() - histogramTime));

            if (graphs.size() == 1) {
                for (int i = 0; i < 2; i++) {
                    List<HashMap<Integer, HashSet<Change>>> changes = new ArrayList<>();
                    String changefilePath = "changes_t" + (i + 1) + "_t" + (i + 2) + "_" + tgfdDiscovery.graphSize + ".json";
                    HashMap<String, org.json.simple.JSONArray> changeFilesMap = new HashMap<>();
                    JSONParser parser = new JSONParser();
                    Object json;
                    org.json.simple.JSONArray jsonArray = new JSONArray();
                    try {
                        json = parser.parse(new FileReader(changefilePath));
                        jsonArray = (org.json.simple.JSONArray) json;
                    } catch (Exception e) {
                        e.printStackTrace();
                    }
                    System.out.println("Storing " + changefilePath + " in memory");
                    changeFilesMap.put(changefilePath, jsonArray);
                    ChangeLoader changeLoader = new ChangeLoader(changeFilesMap.get(changefilePath));
                    HashMap<Integer, HashSet<Change>> newChanges = changeLoader.getAllGroupedChanges();
                    System.out.println("Total number of changes in changefile: " + newChanges.size());
                    changes.add(newChanges);
                    ArrayList<TGFD> tgfds = tgfdDiscovery.getDummyTGFDs();
                    IncUpdates incUpdatesOnDBpedia = new IncUpdates(graphs.get(0).getGraph(), tgfds);
                    incUpdatesOnDBpedia.AddNewVertices(changeLoader.getAllChanges());
                    HashMap<String, TGFD> tgfdsByName = new HashMap<>();
                    for (TGFD tgfd : tgfds) {
                        tgfdsByName.put(tgfd.getName(), tgfd);
                    }
                    for (HashMap<Integer, HashSet<Change>> changesByFile : changes) {
                        for (int changeID : changesByFile.keySet()) {
                            incUpdatesOnDBpedia.updateGraphByGroupOfChanges(changesByFile.get(changeID), tgfdsByName);
                        }
                    }
                    GraphLoader graphLoader = new GraphLoader();
                    graphLoader.setGraph(incUpdatesOnDBpedia.getBaseGraph());
                    graphs.add(graphLoader);
                }
            }

            tgfdDiscovery.initialize(graphs);

            while (tgfdDiscovery.getCurrentVSpawnLevel() <= tgfdDiscovery.getK()) {

                System.out.println("VSpawn level " + tgfdDiscovery.getCurrentVSpawnLevel());
                System.out.println("Previous level node index " + tgfdDiscovery.getPreviousLevelNodeIndex());
                System.out.println("Candidate edge index " + tgfdDiscovery.getCandidateEdgeIndex());

                PatternTreeNode patternTreeNode = null;
                long vSpawnTime = System.currentTimeMillis();
                while (patternTreeNode == null && tgfdDiscovery.getCurrentVSpawnLevel() <= tgfdDiscovery.getK()) {
                    patternTreeNode = tgfdDiscovery.vSpawn();
                }
                vSpawnTime = System.currentTimeMillis() - vSpawnTime;
                TgfdDiscovery.printWithTime("vSpawn", vSpawnTime);
                tgfdDiscovery.addToTotalVSpawnTime(vSpawnTime);
                if (tgfdDiscovery.getCurrentVSpawnLevel() > tgfdDiscovery.getK()) break;
                ArrayList<ArrayList<HashSet<ConstantLiteral>>> matches = new ArrayList<>();
                for (int timestamp = 0; timestamp < tgfdDiscovery.getNumOfSnapshots(); timestamp++) {
                    matches.add(new ArrayList<>());
                }
                long matchingTime = System.currentTimeMillis();

                assert patternTreeNode != null;
                if (tgfdDiscovery.isValidationSearch()) {
                    tgfdDiscovery.getMatchesForPattern(graphs, patternTreeNode, matches);
                    matchingTime = System.currentTimeMillis() - matchingTime;
                    TgfdDiscovery.printWithTime("getMatchesUsingChangefiles", (matchingTime));
                    tgfdDiscovery.addToTotalMatchingTime(matchingTime);
                }
                else if (tgfdDiscovery.isUseChangeFile()) {
                    tgfdDiscovery.getMatchesUsingChangefiles(graphs, patternTreeNode, matches);
                    matchingTime = System.currentTimeMillis() - matchingTime;
                    TgfdDiscovery.printWithTime("getMatchesUsingChangefiles", (matchingTime));
                    tgfdDiscovery.addToTotalMatchingTime(matchingTime);
                }
                else {
                    tgfdDiscovery.findMatchesUsingCenterVertices(graphs, patternTreeNode, matches);
                    matchingTime = System.currentTimeMillis() - matchingTime;
                    TgfdDiscovery.printWithTime("findMatchesUsingCenterVertices", (matchingTime));
                    tgfdDiscovery.addToTotalMatchingTime(matchingTime);
                }

                if (patternTreeNode.getPatternSupport() < tgfdDiscovery.getTheta()) {
                    System.out.println("Mark as pruned. Real pattern support too low for pattern " + patternTreeNode.getPattern());
                    if (!tgfdDiscovery.hasNoSupportPruning()) patternTreeNode.setIsPruned();
                    continue;
                }

                if (tgfdDiscovery.isSkipK1() && tgfdDiscovery.getCurrentVSpawnLevel() == 1) continue;

                final long hSpawnStartTime = System.currentTimeMillis();
                ArrayList<TGFD> tgfds = tgfdDiscovery.hSpawn(patternTreeNode, matches);
                TgfdDiscovery.printWithTime("hSpawn", (System.currentTimeMillis() - hSpawnStartTime));
                tgfdDiscovery.getTgfds().get(tgfdDiscovery.getCurrentVSpawnLevel()).addAll(tgfds);
            }
            tgfdDiscovery.printTimeStatistics();
            final long endTime = System.currentTimeMillis() - tgfdDiscovery.getStartTime();
            System.out.println("Total execution time: " + (endTime));
            runtimes.add(endTime);
        }
        PrintStream logStream = null;
        try {
            logStream = new PrintStream("changefile-test-runtimes-" + overallTimeAndDateStamp + ".txt");
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }
        System.setOut(logStream);
        for (Long runtime: runtimes) {
            System.out.println(runtime);
        }
    }
}
