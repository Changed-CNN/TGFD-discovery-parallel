import Infra.TGFD;
import TgfdDiscovery.TgfdDiscovery;
import changeExploration.*;
import com.fasterxml.jackson.databind.ObjectMapper;
import graphLoader.DBPediaLoader;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.Options;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import util.Config;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

public class testDiffExtractorDbpedia {

    public static double PERCENT = 0.05;

    public static void main(String[] args) throws FileNotFoundException {

        Options options = TgfdDiscovery.initializeCmdOptions();
        options.addOption("percent", true, "percentage of changes to keep");
        CommandLine cmd = TgfdDiscovery.parseArgs(options, args);

        String path = null;
        String graphSize = null;
        if (cmd.hasOption("path")) {
            path = cmd.getOptionValue("path").replaceFirst("^~", System.getProperty("user.home"));
            if (!Files.isDirectory(Path.of(path))) {
                System.out.println(Path.of(path) + " is not a valid directory.");
                return;
            }
            graphSize = Path.of(path).getFileName().toString();
        }

        if (cmd.hasOption("percent")) {
            PERCENT = Double.parseDouble(cmd.getOptionValue("percent"));
        }

        assert path != null;
        ArrayList<File> directories = new ArrayList<>(List.of(Objects.requireNonNull(new File(path).listFiles(File::isDirectory))));
        directories.sort(Comparator.comparing(File::getName));
        StringBuilder str = new StringBuilder();
        int index = 1;
        for (File directory : directories) {
            str.append("-s" + index + " " + directory.getName() + "-01-01\n");
            ArrayList<File> files = new ArrayList<>(List.of(Objects.requireNonNull(new File(directory.getPath()).listFiles(File::isFile))));
            List<String> paths = files.stream().map(File::getPath).collect(Collectors.toList());
            for (String filepath : paths) {
                if (filepath.contains("types")) {
                    str.append("-t" + index + " " + filepath + "\n");
                } else {
                    str.append("-d" + index + " " + filepath + "\n");
                }
            }
            index++;
        }
        str.append("-logcap 1,1,1");

        try {
            BufferedWriter writer = new BufferedWriter(new FileWriter("conf.txt"));
            writer.write(str.toString());
            writer.close();
        } catch (IOException e) {
            e.printStackTrace();
        }

        System.out.println("Test extract diffs over DBPedia graph");

        Config.parse("conf.txt");

        System.out.println(Config.getAllDataPaths().keySet() + " *** " + Config.getAllDataPaths().values());
        System.out.println(Config.getAllTypesPaths().keySet() + " *** " + Config.getAllTypesPaths().values());

        HashMap<Integer, ArrayList<Model>> typeModelHashMap = new HashMap<>();
        for (int i = 1; i <= 3; i++) {
            typeModelHashMap.put(i, new ArrayList<>());
            for (String pathString : Config.getAllTypesPaths().get(i)) {
                System.out.println("Reading " + pathString);
                Model model = ModelFactory.createDefaultModel();
                Path input = Paths.get(pathString);
                model.read(input.toUri().toString());
                typeModelHashMap.get(i).add(model);
            }
        }

        HashMap<Integer, ArrayList<Model>> dataModelHashMap = new HashMap<>();
        for (int i = 1; i <= 3; i++) {
            dataModelHashMap.put(i, new ArrayList<>());
            for (String pathString : Config.getAllDataPaths().get(i)) {
                System.out.println("Reading " + pathString);
                Model model = ModelFactory.createDefaultModel();
                Path input = Paths.get(pathString);
                model.read(input.toUri().toString());
                dataModelHashMap.get(i).add(model);
            }
        }

        System.out.println("Generating the diff files for the TGFD: " + graphSize);
        Object[] ids = dataModelHashMap.keySet().toArray();
        Arrays.sort(ids);
        DBPediaLoader first, second = null;
        List<Change> allChanges;
        int t1, t2 = 0;
        for (int i = 0; i < ids.length; i += 2) {

            System.out.println("===========Snapshot (" + ids[i] + ")===========");
            long startTime = System.currentTimeMillis();

            t1 = (int) ids[i];
            first = new DBPediaLoader(new ArrayList<>(), typeModelHashMap.get((int) ids[i]),
                    dataModelHashMap.get((int) ids[i]));

            printWithTime("Load graph (" + ids[i] + ")", System.currentTimeMillis() - startTime);

            if (second != null) {
                ChangeFinder cFinder = new ChangeFinder(second, first, new ArrayList<>());
                allChanges = cFinder.findAllChanged();

                analyzeChanges(allChanges, new ArrayList<>(), second.getGraphSize(), cFinder.getNumberOfEffectiveChanges(), t2, t1, graphSize, Config.getDiffCaps());
            }

            if (i + 1 >= ids.length)
                break;

            System.out.println("===========Snapshot (" + ids[i + 1] + ")===========");
            startTime = System.currentTimeMillis();

            t2 = (int) ids[i + 1];
            second = new DBPediaLoader(new ArrayList<>(), typeModelHashMap.get((int) ids[i + 1]),
                    dataModelHashMap.get((int) ids[i + 1]));

            printWithTime("Load graph (" + ids[i + 1] + ")", System.currentTimeMillis() - startTime);

            ChangeFinder cFinder = new ChangeFinder(first, second, new ArrayList<>());
            allChanges = cFinder.findAllChanged();

            analyzeChanges(allChanges, new ArrayList<>(), first.getGraphSize(), cFinder.getNumberOfEffectiveChanges(), t1, t2, graphSize, Config.getDiffCaps());

        }
    }

    private static void analyzeChanges(List<Change> allChanges, List<TGFD> allTGFDs, int graphSize,
                                       int changeSize, int timestamp1, int timestamp2, String TGFDsName, ArrayList<Double> diffCaps) {
//        ChangeTrimmer trimmer=new ChangeTrimmer(allChanges,allTGFDs);
//        for (double i:diffCaps)
//        {
//            int allowedNumberOfChanges= (int) (i*graphSize);
//            if (allowedNumberOfChanges<changeSize)
//            {
//                List<Change> trimmedChanges=trimmer.trimChanges(allowedNumberOfChanges);
//                saveChanges(trimmedChanges,timestamp1,timestamp2,TGFDsName + "_" + i);
//            }
//            else
//            {
        saveChanges(allChanges, timestamp1, timestamp2, TGFDsName);
//                return;
//            }
//        }
    }

    private static void printWithTime(String message, long runTimeInMS) {
        System.out.println(message + " time: " + runTimeInMS + "(ms) ** " +
                TimeUnit.MILLISECONDS.toSeconds(runTimeInMS) + "(sec) ** " +
                TimeUnit.MILLISECONDS.toMinutes(runTimeInMS) + "(min)");
    }

    private static void printStatistics(List<Change> allChanges) {
        int insertChangeEdge = 0;
        int insertChangeVertex = 0;
        int insertChangeAttribute = 0;
        int deleteChangeEdge = 0;
        int deleteChangeVertex = 0;
        int deleteChangeAttribute = 0;
        int changeAttributeValue = 0;

        for (Change c : allChanges) {
            if (c instanceof EdgeChange) {
                if (c.getTypeOfChange() == ChangeType.deleteEdge)
                    deleteChangeEdge++;
                else if (c.getTypeOfChange() == ChangeType.insertEdge)
                    insertChangeEdge++;
            } else if (c instanceof VertexChange) {
                if (c.getTypeOfChange() == ChangeType.deleteVertex)
                    deleteChangeVertex++;
                else if (c.getTypeOfChange() == ChangeType.insertVertex)
                    insertChangeVertex++;
            } else if (c instanceof AttributeChange) {
                if (c.getTypeOfChange() == ChangeType.deleteAttr)
                    deleteChangeAttribute++;
                else if (c.getTypeOfChange() == ChangeType.insertAttr)
                    insertChangeAttribute++;
                else
                    changeAttributeValue++;
            }
        }
        System.out.println("Total number of changes: " + allChanges.size());
        System.out.println("Edges: +" + insertChangeEdge + " ** -" + deleteChangeEdge);
        System.out.println("Vertices: +" + insertChangeVertex + " ** -" + deleteChangeVertex);
        System.out.println("Attributes: +" + insertChangeAttribute + " ** -" + deleteChangeAttribute + " ** updates: " + changeAttributeValue);
    }

    private static void saveChanges(List<Change> allChanges, int t1, int t2, String tgfdName) {

        System.out.println("Number of changes: " + allChanges.size());
        int numOfChangesToConsider = (int) (allChanges.size() * PERCENT);
        System.out.println("Number of changes considered: " + numOfChangesToConsider);
        Collections.shuffle(allChanges);
        List<Change> changesToConsider = allChanges.subList(0, numOfChangesToConsider);

        System.out.println("Printing the changes: " + t1 + " -> " + t2);

        HashMap<ChangeType, Integer> map = new HashMap<>();
        map.put(ChangeType.deleteAttr, 1);
        map.put(ChangeType.insertAttr, 2);
        map.put(ChangeType.changeAttr, 2);
        map.put(ChangeType.deleteEdge, 3);
        map.put(ChangeType.insertEdge, 4);
        map.put(ChangeType.deleteVertex, 5);
        map.put(ChangeType.insertVertex, 5);
        changesToConsider.sort(new Comparator<Change>() {
            @Override
            public int compare(Change o1, Change o2) {
                return map.get(o1.getTypeOfChange()).compareTo(map.get(o2.getTypeOfChange()));
            }
        });
        try {
            FileWriter file = new FileWriter("./changes_t" + t1 + "_t" + t2 + "_" + tgfdName + ".json");
            file.write("[");
            for (int index = 0; index < changesToConsider.size(); index++) {
                Change change = changesToConsider.get(index);
                final StringWriter sw = new StringWriter();
                final ObjectMapper mapper = new ObjectMapper();
                mapper.writeValue(sw, change);
                file.write(sw.toString());
                if (index < changesToConsider.size() - 1) {
                    file.write(",");
                }
                sw.close();
            }
            file.write("]");
            System.out.println("Successfully wrote to the file.");
            file.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
        printStatistics(changesToConsider);
    }
}
