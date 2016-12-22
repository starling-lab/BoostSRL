/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.Sentence;
import java.util.List;
import edu.wisc.cs.will.FOPC.AllOfFOPC;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.ResThmProver.VariantClauseAction;
import edu.wisc.cs.will.Utils.MessageType;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import java.io.File;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.EnumSet;
import java.util.Properties;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author twalker
 */
public class TAWExperimenter {

    String rootPath = "/scratch/twalker/development/BL_rawData/";

    String pathSuffix = "";

    boolean useNameForDirectory = false;

    int maxTimeInMilliseconds = 180000;

    public TAWExperimenter() {
    }

    public static void setUpClass() {
        //AdviceProcessor.debugLevel = 2;

        Utils.addFilteredMessageType(EnumSet.allOf(MessageType.class));
        Utils.setVerbosity(Utils.Verbosity.Developer);

    }

    
    public void checkMissing() throws SearchInterrupted, IOException {
        MyExperimenter e = new MyExperimenter(true);
        MyExperimenter.checkWhatIsMissing = true;

        MyExperimenter.mainJWS(new String[0], false, e);
    }

    public void generateAdviceNoise() throws SearchInterrupted, IOException {
        MyExperimenter e = new MyExperimenter(true);
        MyExperimenter.createAdviceNoiseFiles = true;

        MyExperimenter.mainJWS(new String[0], false, e);
    }

    public void generateExampleNoise() throws SearchInterrupted, IOException {
        MyExperimenter e = new MyExperimenter(false);
        MyExperimenter.createDataFilesOnly = true;

        MyExperimenter.mainJWS(new String[0], false, e);
    }

    // <editor-fold defaultstate="collapsed" desc="Advice">


    public void generateNoisyData() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);


        String domain = "UAV/";
        String prefix = "ReadyToFly";
        String name = "uavReadyToFlyCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        //main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, true);
    }

    public void readyToFlyGenerated() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);


        String domain = "UAV/";
        String prefix = "ReadyToFly";
        String name = "uavReadyToFlyCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, true);
    }

    //////@Test
    public void fullFuelTankGenerated() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);

        Properties p = System.getProperties();

        String domain = "UAV/";
        String prefix = "Full";
        String name = "uavFullFuelTankCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, true);
    }

    ////@Test
    public void nearGenerated() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);

        Properties p = System.getProperties();

        String domain = "UAV/";
        String prefix = "Near";
        String name = "uavNearCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion"/*, "-maxTime=200000"*/};
        startILP(main, args, relevancePath, true);
    }

    ////@Test
    public void assesGoalGenerated() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);

        Properties p = System.getProperties();

        String domain = "UAV/";
        String prefix = "AssessGoal";
        String name = "uavAssessGoalCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, true);
    }

    ////@Test
    public void isStoppedTruck() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);

        Properties p = System.getProperties();

        String domain = "UAV/";
        String prefix = "IsASingleStoppedTruckScenario";
        String name = "uavUnit4RecognizeSingleStoppedTruckScenariosCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, true);
    }

    ////@Test
    public void isMovingTruck() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);

        //Experimenter.createAdviceNoiseFiles = true;

        Properties p = System.getProperties();

        String domain = "UAV/";
        String prefix = "IsASingleMovingTruckScenario";
        String name = "uavUnit4RecognizeSingleMovingTruckScenariosCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};

        main.onionFilter = new MyOnionFilter();

        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, true);
    }

    ////@Test
    public void isTruckIsAtIntersection() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);

        Properties p = System.getProperties();

        String domain = "UAV/";
        String prefix = "TruckIsAtIntersection";
        String name = "uavUnit4TruckIsAtIntersectionCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, true);
    }

    ////@Test
    public void isCompanyHasMinePlow() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);

        Properties p = System.getProperties();

        String domain = "ATF/";
        String prefix = "CompanyHasMinePlow";
        String name = "atfCompanyHasMinePlowCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, true);
    }

    ////@Test
    public void isCallsForColumnFormation() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);

        Properties p = System.getProperties();

        String domain = "ATF/";
        String prefix = "CallsForColumnFormation";
        String name = "callsForColumnFormationCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};

        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, true);
    }

    ////@Test
    public void isCallsForEchelonLFormation() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);

        Properties p = System.getProperties();

        String domain = "ATF/";
        String prefix = "CallsForEchelonLFormation";
        String name = "callsForEchelonLFormationCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, true);
    }

    ////@Test
    public void iscallsForEchelonRFormationCBE() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);

        Properties p = System.getProperties();

        String domain = "ATF/";
        String prefix = "CallsForEchelonRFormation";
        String name = "callsForEchelonRFormationCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, true);
    }

    ////@Test
    public void isCallsForLineFormation() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);

        Properties p = System.getProperties();

        String domain = "ATF/";
        String prefix = "CallsForLineFormation";
        String name = "callsForLineFormationCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, true);
    }

    ////@Test
    public void iscallsForVeeFormationCBE() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);

        Properties p = System.getProperties();

        String domain = "ATF/";
        String prefix = "CallsForVeeFormation";
        String name = "callsForVeeFormationCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, true);
    }

    ////@Test
    public void iscallsForWedgeFormationCBE() throws SearchInterrupted, FileNotFoundException, IOException, IOException {
        Experimenter main = new MyExperimenter(true);

        Properties p = System.getProperties();

        String domain = "ATF/";
        String prefix = "CallsForWedgeFormation";
        String name = "callsForWedgeFormationCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, true);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="NoAdvice">
////////@Test
    public void readyToFlyGeneratedNoAdvice() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(false);


        String domain = "UAV/";
        String prefix = "ReadyToFly";
        String name = "uavReadyToFlyCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, false);
    }

    ////////@Test
    public void fullFuelTankGeneratedNoAdvice() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(false);

        Properties p = System.getProperties();

        String domain = "UAV/";
        String prefix = "Full";
        String name = "uavFullFuelTankCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, false);
    }

    ////////@Test
    public void nearGeneratedNoAdvice() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(false);

        Properties p = System.getProperties();

        String domain = "UAV/";
        String prefix = "Near";
        String name = "uavNearCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion"/*, "-maxTime=200000"*/};
        startILP(main, args, relevancePath, false);
    }

    ////////@Test
    public void assesGoalGeneratedNoAdvice() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(false);

        Properties p = System.getProperties();

        String domain = "UAV/";
        String prefix = "AssessGoal";
        String name = "uavAssessGoalCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, false);
    }

    ////////@Test
    public void isStoppedTruckGoalGeneratedNoAdvice() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(false);

        Properties p = System.getProperties();

        String domain = "UAV/";
        String prefix = "IsASingleStoppedTruckScenario";
        String name = "uavUnit4RecognizeSingleStoppedTruckScenariosCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, false);
    }

    ////////@Test
    public void isSingleMovingTruckNoAdvice() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(false);

        Properties p = System.getProperties();

        String domain = "UAV/";
        String prefix = "IsASingleMovingTruckScenario";
        String name = "uavUnit4RecognizeSingleMovingTruckScenariosCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, false);
    }

    ////////@Test
    public void isTruckIsAtIntersectionNoAdvice() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(false);

        Properties p = System.getProperties();

        String domain = "UAV/";
        String prefix = "TruckIsAtIntersection";
        String name = "uavUnit4TruckIsAtIntersectionCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, false);
    }

    ////////@Test
    public void isCompanyHasMinePlowNoAdvice() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(false);

        Properties p = System.getProperties();

        String domain = "ATF/";
        String prefix = "CompanyHasMinePlow";
        String name = "atfCompanyHasMinePlowCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, false);
    }

    ////////@Test
    public void isCallsForColumnFormationNoAdvice() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(false);

        Properties p = System.getProperties();

        String domain = "ATF/";
        String prefix = "CallsForColumnFormation";
        String name = "callsForColumnFormationCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, false);
    }

    ////////@Test
    public void isCallsForEchelonLFormationNoAdvice() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(false);

        Properties p = System.getProperties();

        String domain = "ATF/";
        String prefix = "CallsForEchelonLFormation";
        String name = "callsForEchelonLFormationCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, false);
    }

    ////////@Test
    public void iscallsForEchelonRFormationNoAdvice() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(false);

        Properties p = System.getProperties();

        String domain = "ATF/";
        String prefix = "CallsForEchelonRFormation";
        String name = "callsForEchelonRFormationCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, false);
    }

    ////////@Test
    public void isCallsForLineFormationNoAdvice() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(false);

        Properties p = System.getProperties();

        String domain = "ATF/";
        String prefix = "CallsForLineFormation";
        String name = "callsForLineFormationCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, false);
    }

    ////////@Test
    public void iscallsForVeeFormationNoAdvice() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(false);

        Properties p = System.getProperties();

        String domain = "ATF/";
        String prefix = "CallsForVeeFormation";
        String name = "callsForVeeFormationCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, false);
    }

    ////////@Test
    public void iscallsForWedgeFormationNoAdvice() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(false);

        Properties p = System.getProperties();

        String domain = "ATF/";
        String prefix = "CallsForWedgeFormation";
        String name = "callsForWedgeFormationCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        File relevancePath = new CondorFile(file_string, prefix + "_bkRel.txt");

        main.lessonsToUse = new String[]{prefix};
        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        startILP(main, args, relevancePath, false);
    }
    // </editor-fold>

    private void startILP(Experimenter main, String[] args, File relevancePath, boolean adviceEnabled, String... additionBK) throws SearchInterrupted, FileNotFoundException, IOException, IOException {


        AllOfFOPC.renameVariablesWhenPrinting = true;


        Utils.setVerbosity(Utils.Verbosity.DeveloperNoWait);
        main.getContext().getStringHandler().setVarientClauseHandling(VariantClauseAction.SILENTLY_REMOVE_VARIANTS);
        main.getContext().getStringHandler().printVariableCounters = true;

        if (additionBK != null) {
            for (String string : additionBK) {
                main.getContext().assertDefiniteClause(string);
            }
        }

        Experimenter.mainJWS(args, false, main);

//        if (main.bestTheoryTrainingScore != null) {
//            throw new RuntimeException("No training results.  No theory learned?");
//        }
//        if (main.bestTheoryTrainingScore.getAccuracy() > 0.99) {
//            throw new RuntimeException("Insufficient Trainset Accuracy");
//        }
    }

    ////@Test
    public void checkMovingTruckTheory() throws SearchInterrupted, FileNotFoundException, IOException {
        Experimenter main = new MyExperimenter(true);

        Properties p = System.getProperties();

//        String domain = "UAV/";
//        String prefix = "IsASingleMovingTruckScenario";
//        String name = "uavUnit4RecognizeSingleMovingTruckScenariosCBE";

        String domain = "ATF/";
        String prefix = "CallsForColumnFormation";
        String name = "callsForColumnFormationCBE";

        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;


        main.relevanceEnabled = true;
        main.lessonsToUse = new String[]{prefix};

        main.onionFilter = new MyOnionFilter();
        main.directory = file_string;

        AdviceProcessor.debugLevel = 0;

        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
        main.setup(args);

//        String theoryString = "ilPred_IsASingleMovingTruckScenario(?A, ?B, ?C, ?D) :- megaNotPosAndNegAnd251(?A, ?B, ?C, ?D)." +
//                        "ilPred_IsASingleMovingTruckScenario(?A, ?B, ?C, ?D) :- and_advice_high_257(?A, ?B, ?C, ?D). ";

        //String theoryString = "ilPred_IsASingleMovingTruckScenario(?A, ?B, ?C, ?D) :- \\+(megaNotPosAndNegAnd251(?A, ?B, ?C, ?D)).";//, \\+(and_advice_high_257(?A, ?B, ?C, ?D)). ";

        //String theoryString = "ilPred_IsASingleMovingTruckScenario(?A, ?B, ?C, ?D) :- megaPosAndNotNegAnd0(?A, ?B, ?C, ?D). ";
        //String theoryString = "ilPred_IsASingleMovingTruckScenario(?A, ?B, ?C, ?D) :- and_advice_high_10(?A, ?B, ?C, ?D).";

        String theoryString = "ilPred_CallsForColumnFormation(?A, ?B, ?C, ?D) :- and_advice_high_67(?A, ?B, ?C, ?D).";

        String supportClausesString = "and_advice_high_67(?A, ?B, ?C, ?D) :-"
                + "ilField_Segment_loc(?A, ?B, ?E, ?D),"
                + "sameAsIL(?A, unlikely, ?E, ?D),"
                + "ilField_Segment_relativeDirectionOfEnemy(?A, ?B, ?F, ?D),"
                + "inBetweenCC(90, ?F, 270). ";




//        String supportClausesString =
//                "and_advice_high_10(?A, ?B, ?C, ?D) :- "
//                + "   ilField_Vehicle_moveStatus(?A, ?E, ?F, ?D),"
//                + "  sameAsIL(?A, ?F, symbol_Moving, ?D),"
//                + "   ilField_Scenario_actors(?A, ?B, ?G, ?D),"
//                + "   length(?G, ?H),"
//                + "   sameAsIL(?A, 1, ?H, ?D),"
//                + "   ilField_Scenario_actors(?A, ?B, ?I, ?D),"
//                + "   member(?E, ?I),"
//                + "   ilType_Truck(?A, ?E, ?D).\n"
//                + "megaPosAndNotNegAnd0(?A, ?B, ?C, ?D) :- "
//                + "wi_pred1(?A, ?B, ?E, ?D), ilField_Vehicle_moveStatus(?A, ?E, ?F, ?D), differentIL(?A, symbol_Moving, ?F, ?D), ilField_Vehicle_moveStatus(?A, ?G, ?H, ?D), sameAsIL(?A, ?H, ?H, ?D), ilField_Vehicle_moveStatus(?A, ?G, ?H, ?D), sameAsIL(?A, ?H, ?H, ?D), wi_pred1(?A, ?B, ?G, ?D), ilType_Truck(?A, ?G, ?D), ilField_Scenario_actors(?A, ?B, ?I, ?D),"
//                + "length(?I, ?J), sameAsIL(?A, ?K, ?J, ?D), ilField_Vehicle_moveStatus(?A, ?G, ?H, ?D), sameAsIL(?A, ?H, ?H, ?D), ilField_Scenario_actors(?A, ?B, ?I, ?D), length(?I, ?J), sameAsIL(?A, ?K, ?J, ?D), ilField_Scenario_actors(?A, ?B, ?I, ?D), length(?I, ?J), sameAsIL(?A, ?K, ?J, ?D),"
//                + "ilField_Vehicle_moveStatus(?A, ?G, ?H, ?D), sameAsIL(?A, ?H, ?H, ?D), wi_pred1(?A, ?B, ?G, ?D), ilType_Truck(?A, ?G, ?D), wi_pred1(?A, ?B, ?G, ?D), ilType_Truck(?A, ?G, ?D), ilField_Scenario_actors(?A, ?B, ?I, ?D), length(?I, ?J), sameAsIL(?A, ?K, ?J, ?D), wi_pred1(?A, ?B, ?G, ?D),"
//                + "ilType_Truck(?A, ?G, ?D), wi_pred15(?A, ?B, ?L, ?D), wi_pred41(?A, ?L, ?D), ilField_Scenario_actors(?A, ?B, ?M, ?D), length(?M, ?N), differentIL(?A, ?N, 1, ?D), \\+(\\+(\\+(wi_pred15(?A, ?B, Person_5366, ?D))), \\+(ilField_Vehicle_moveStatus(?A, Truck_233, ?P, ?D), sameAsIL(?A, ?P, ?P, ?D))).\n"
//                + "wi_pred15(?A, ?B, Person_5366, ?C) :- "
//                + "ilField_Scenario_actors(?A, ?B, ?D, ?C),"
//                + "member(Person_5366, ?D),"
//                + "ilType_Truck(?A, Person_5366, ?C).\n "
//                + "wi_pred1(?A, ?B, ?C, ?D) :- "
//                + "ilField_Scenario_actors(?A, ?B, ?E, ?D),"
//                + "member(?C, ?E).\n "
//                + "wi_pred15(?A, ?B, ?C, ?D) :- "
//                + "ilField_Scenario_actors(?A, ?B, ?E, ?D),"
//                + "member(?C, ?E),"
//                + "ilType_Truck(?A, ?C, ?D).\n"
//                + "wi_pred41(?A, ?B, ?C) :- "
//                + "ilField_Vehicle_moveStatus(?A, ?B, ?D, ?C),"
//                + "sameAsIL(?A, symbol_Moving, ?D, ?C).\n "
//                + "megaNotPosAndNegAnd251(?A, ?B, ?C, ?D) :- "
//                + "\\+(ilField_Scenario_actors(?A, ?B, ?E, ?D), "
//                + "  length(?E, ?F), "
//                + "  differentIL(?A, ?F, 1, ?D), "
//                + "  \\+(ilField_Scenario_actors(?A, ?B, ?G, ?D),"
//                + "      length(?G, ?H),"
//                + "      sameAsIL(?A, ?I, ?H, ?D)), "
//                + "  \\+(wi_pred1(?A, ?B, ?J, ?D),"
//                + "      ilType_Truck(?A, ?J, ?D)), "
//                + "  \\+(ilField_Vehicle_moveStatus(?A, ?J, ?K, ?D),"
//                + "      sameAsIL(?A, ?K, ?K, ?D),"
//                + "      ilField_Scenario_actors(?A, ?B, ?G, ?D),"
//                + "      length(?G, ?H),"
//                + "      sameAsIL(?A, ?I, ?H, ?D)), "
//                + "  \\+(wi_pred1(?A, ?B, ?J, ?D),"
//                + "      ilType_Truck(?A, ?J, ?D),"
//                + "      ilField_Scenario_actors(?A, ?B, ?G, ?D),"
//                + "      length(?G, ?H),"
//                + "      sameAsIL(?A, ?I, ?H, ?D)), "
//                + "  \\+(ilField_Vehicle_moveStatus(?A, ?J, ?K, ?D),"
//                + "      sameAsIL(?A, ?K, ?K, ?D),"
//                + "      wi_pred1(?A, ?B, ?J, ?D),"
//                + "      ilType_Truck(?A, ?J, ?D),"
//                + "      ilField_Scenario_actors(?A, ?B, ?G, ?D),"
//                + "      length(?G, ?H),"
//                + "      sameAsIL(?A, ?I, ?H, ?D)), "
//                + "  \\+(ilField_Vehicle_moveStatus(?A, ?J, ?K, ?D),"
//                + "      sameAsIL(?A, ?K, ?K, ?D),"
//                + "      wi_pred1(?A, ?B, ?J, ?D),"
//                + "     ilType_Truck(?A, ?J, ?D)), "
//                + "  \\+(ilField_Vehicle_moveStatus(?A, ?J, ?K, ?D),"
//                + "      sameAsIL(?A, ?K, ?K, ?D)), "
//                + "  wi_pred1(?A, ?B, ?L, ?D), "
//                + "  ilField_Vehicle_moveStatus(?A, ?L, ?M, ?D), "
//                + "  differentIL(?A, symbol_Moving, ?M, ?D), "
//                + "  ilField_Vehicle_moveStatus(?A, Truck_233, ?N, ?D), "
//                + "  sameAsIL(?A, ?N, ?N, ?D), "
//                + "  \\+(wi_pred15(?A, ?B, Person_5366, ?D))"
//                + "),"
//                + "\\+(wi_pred15(?A, ?B, ?P, ?D),"
//                + "    wi_pred41(?A, ?P, ?D)"
//                + ").\n "
//                + "and_advice_high_257(?A, ?B, ?C, ?D) :- "
//                + "ilField_Scenario_actors(?A, ?B, ?E, ?D),"
//                + "length(?E, ?F),"
//                + "differentIL(?A, ?F, 1, ?D).\n"
//                + "wi_pred1(?A, ?B, ?C, ?D) :- "
//                + "ilField_Scenario_actors(?A, ?B, ?E, ?D),"
//                + "member(?C, ?E).\n "
//                + "wi_pred15(?A, ?B, ?C, ?D) :- "
//                + "wi_pred1(?A, ?B, ?C, ?D),"
//                + "ilType_Truck(?A, ?C, ?D).\n ";

        List<Sentence> theoryClauses = main.getContext().getFileParser().parse(theoryString);
        List<Sentence> supportClauses = main.getContext().getFileParser().parse(supportClausesString);

        Theory t = new Theory(main.getContext().getStringHandler());
        for (Sentence sentence : theoryClauses) {
            t.addMainClause(sentence.convertToClausalForm().get(0), null);
        }

        for (Sentence sentence : supportClauses) {
            t.addSupportingClause(sentence.convertToClausalForm().get(0), null);
        }

        System.out.println(t);

        CoverageScore testCoverage = main.getTestSetScore(main.getContext().getStringHandler().getPredicateName("ilPred_IsASingleMovingTruckScenario"), t);

        System.out.println(testCoverage);

        if (testCoverage.getAccuracy() > 0.99 || testCoverage.getAccuracy() < 0.01) {
            throw new RuntimeException("Insufficient Trainset Accuracy");
        }
    }

    ////@Test
//    public void checkMovingTruckAdvicePieceAccuracy() throws SearchInterrupted, FileNotFoundException, IOException {
//        Experimenter main = new MyExperimenter(true);
//
//        Properties p = System.getProperties();
//
////        String domain = "UAV/";
////        String prefix = "IsASingleMovingTruckScenario";
////        String name = "uavUnit4RecognizeSingleMovingTruckScenariosCBE";
//
//        String domain = "ATF/";
//        String prefix = "CallsForColumnFormation";
//        String name = "callsForColumnFormationCBE";
//
//        String file_string = rootPath + (useNameForDirectory ? domain + name : prefix) + pathSuffix;
//
//
//        main.relevanceEnabled = true;
//        main.lessonsToUse = new String[]{prefix};
//
//        main.onionFilter = new MyOnionFilter();
//        main.directory = file_string;
//
//        AdviceProcessor.debugLevel = 0;
//
//        String[] args = new String[]{"-prefix=" + prefix, "-onion", "-maxTime=" + maxTimeInMilliseconds};
//        main.setup(args);
//
//        List<Example> positiveExamples = main.getLearnOneClause().getPosExamples();
//        List<Example> negativeExamples = main.getLearnOneClause().getNegExamples();
//
//        List<Example> uniquePositiveAdviceExamples = main.getLearnOneClause().getAdviceProcessor().getExamplesWithUniqueAdvice(positiveExamples);
//        List<Example> uniqueNegativeAdviceExamples = main.getLearnOneClause().getAdviceProcessor().getExamplesWithUniqueAdvice(negativeExamples);
//
//        for (Example example : uniquePositiveAdviceExamples) {
//            List<RelevantClauseInformation> positiveAdvice = main.getLearnOneClause().getAdviceProcessor().getRelevantClausesForExample(example);
//
//            for (RelevantClauseInformation rci : positiveAdvice) {
//                RelevantClauseInformation generalRCI = rci.getGeneralizeRelevantInformation();
//
//                Clause mergedClause = main.getContext().getStringHandler().getClause(Collections.singletonList((Literal) generalRCI.getExample()), generalRCI.getClause().posLiterals);
//
//                CoverageScore cs = main.getLearnOneClause().getWeightedCoverage(mergedClause, positiveExamples, negativeExamples);
//
//
//                System.out.println(example + ": " + mergedClause);
//                System.out.println("");
//                System.out.println(cs);
//                System.out.println("");
//                System.out.println("");
//            }
//        }
//
//
//    }

    public static void main(String[] args) {
        setUpClass();

        TAWExperimenter e = new TAWExperimenter();
        try {
            e.fullFuelTankGenerated();
        } catch (SearchInterrupted ex) {
            Logger.getLogger(TAWExperimenter.class.getName()).log(Level.SEVERE, null, ex);
        } catch (FileNotFoundException ex) {
            Logger.getLogger(TAWExperimenter.class.getName()).log(Level.SEVERE, null, ex);
        } catch (IOException ex) {
            Logger.getLogger(TAWExperimenter.class.getName()).log(Level.SEVERE, null, ex);
        }

    }

    public class MyExperimenter extends Experimenter {

        boolean myUseAdvice; // Just so we can set it here and update it interface setupUserOverrides()

        public MyExperimenter(boolean myUseAdvice) {
            this.myUseAdvice = myUseAdvice;
        }

        public void setupUserOverrides() {
            experimentName = "BL_rawData/";
            mainWorkingDir = "/scratch/twalker/development/" + experimentName;
            //mainWorkingDir = "/u/shavlikgroup/Jude/Testbeds/" + experimentName;

            //generateExampleNoise = false;

//            fractionOfTrainingExamplesToUse = 1.0;
 //           probOfFlippingClassLabel = 0.03;
 //           probOfDroppingLiteral = 30.0;
//
//            useAdvice = myUseAdvice;
//
//            runNumberFirst = 1;
//            runNumberLast  = 3;

            probOfFlippingClassLabel = 0;
            fractionOfTrainingExamplesToUse = 0.25;
            probOfDroppingLiteral = 0.75;

            //onionFilter = new MyOnionFilter();

            setOverWriteOldResults(true);

            if ( probOfFlippingClassLabel < 0 || probOfFlippingClassLabel >= 1 ) {
                throw new IllegalArgumentException("What the hell.  Check the prob of flipping class label value!");
            }
        }
    }

    public static class MyOnionFilter extends OnionFilter {

        int count = 0;

        @Override
        public boolean skipThisSetting(ILPparameterSettings setting, boolean report) {

            return false;
            
//            if ( setting.getOnionLayer() == 8 ) {
//                return false;
//            }
//
//            if (setting.getMaxNumberOfCycles() != 2) {
//                return true;
//            }
//            if (setting.getMaxNumberOfClauses() != 1) {
//                return true;
//            }
//            if (setting.getMaxNodesToCreate() != 125) {
//                return true;
//            }
//            if (setting.getMaxNodesToConsider() != 10) {
//                return true;
//            }
//            if (setting.getMinPosCoverage() != 0.7500) {
//                return true;
//            }
//            if (setting.getMaxNegCoverage() != 0.9998) {
//                return true;
//            }
//            if (setting.getMinPrecision() != 0.75) {
//                return true;
//            }
//            if (setting.getMEstimatePos() != 0.01) {
//                return true;
//            }
//            if (setting.getMEstimateNeg() != 0.01) {
//                return true;
//            }
//            if (setting.getMinimumStrength() != RelevanceStrength.NEUTRAL) {
//                return true;
//            }


            // return false;

        }
    }
}
