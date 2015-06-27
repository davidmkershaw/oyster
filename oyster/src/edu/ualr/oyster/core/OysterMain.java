/*
 * Copyright 2010 John Talburt, Eric Nelson
 *
 * This file is part of Oyster created in the ERIQ Research Center at University of Arkansas at Little Rock.
 * 
 * Oyster is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * Oyster is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with Oyster.  If not, see <http://www.gnu.org/licenses/>.
 * 
 */

package edu.ualr.oyster.core;

import edu.ualr.oyster.ErrorFormatter;
import edu.ualr.oyster.OysterExplanationFormatter;
import edu.ualr.oyster.association.matching.OysterComparator;
import edu.ualr.oyster.association.matching.OysterCompareDefault;
import edu.ualr.oyster.data.ClusterRecord;
import edu.ualr.oyster.data.ClusterRecordSet;
import edu.ualr.oyster.data.ClusterTypes;
import edu.ualr.oyster.data.CoDoSAOIR;
import edu.ualr.oyster.data.OysterIdentityRecord;
import edu.ualr.oyster.data.OysterIdentityRecordMap;
import edu.ualr.oyster.data.RecordTypes;
import edu.ualr.oyster.er.OysterAssertionEngine;
import edu.ualr.oyster.er.OysterClusterEngine;
import edu.ualr.oyster.er.OysterEngine;
import edu.ualr.oyster.er.OysterMergeConsolidationEngine;
import edu.ualr.oyster.er.OysterMergeEngine;
import edu.ualr.oyster.er.OysterResolutionEngine;
import edu.ualr.oyster.index.Index;
import edu.ualr.oyster.index.IndexRule;
import edu.ualr.oyster.index.NullIndex;
import edu.ualr.oyster.index.TalburtZhouInvertedIndex;
import edu.ualr.oyster.io.AttributesParser;
import edu.ualr.oyster.io.OysterDatabaseReader;
import edu.ualr.oyster.io.OysterDatabaseWriter;
import edu.ualr.oyster.io.OysterDelimitedReader;
import edu.ualr.oyster.io.OysterFixedWidthReader;
import edu.ualr.oyster.io.RunScriptParser;
import edu.ualr.oyster.io.SourceDescriptorParser;
import edu.ualr.oyster.kb.DBEntityMap;
import edu.ualr.oyster.kb.EntityMap;
import edu.ualr.oyster.kb.ModificationRecord;
import edu.ualr.oyster.kb.OysterIdentityRepository;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.Formatter;
import java.util.GregorianCalendar;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Locale;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TimeZone;
import java.util.Timer;
import java.util.TimerTask;
import java.util.TreeMap;
import java.util.logging.FileHandler;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker ">
// #[regen=yes,id=DCE.59177C02-1066-210A-E05F-F9F0D1A34C39]
// </editor-fold>
public class OysterMain {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.E2CBC7ED-318F-1C52-1F67-F595C7E63ECD]
    // </editor-fold>
    /** */
    private OysterIdentityRepository repository = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.673A0DE5-1B5F-FC02-D555-1BFE9BE293A1]
    // </editor-fold>
    /** */
    private OysterAttributes attributes = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.09D24364-CFD2-9D55-1A9D-4C438427ABBE]
    // </editor-fold>
    /** */
    private OysterEngine engine = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.17458F57-08EB-F441-6EA3-99AE0124CF62]
    // </editor-fold>
    /** */
    private OysterRunScript runScript = null;

    private static Index index = null;
    
    private static EntityMap entityMap = null;
    /** */
    private TreeMap<Integer, OysterReferenceSource> sources = null;

    /** */
    private Set<String> passThruAttributes = null;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.54D9233C-EA57-73DE-4FA9-26F71D25FE70]
    // </editor-fold>
    /** */
    private String version = "3.3";

    /** */
    private Logger logger = null;

    /** */
    private OysterReferenceSource source = null;

    /** */
    private Set<String> sourceNames = null;
    
    /** */
    private FileHandler fileHandler = null;

    // Stat/Report fields
    private String startTime, stopTime;
    private long totalRecords = 0;
    private long totalRSwooshs = 0;
    private long groups = 0;
    private long maxGroupSize = 0;
    private long minGroupSize = 1;
    private long minGroupSizeGT1 = 0;
    private TreeMap<Long, Long> clusterFreq = null;
    private long avgClusterGroup = 0;
    private long avgClusterCount = 0;
    private double avgClusterSize = 0;
    private double duplicationRate = 0;
    private Map<String, Long> ruleFreq = null;
    private Map<String, Long> completeRuleFiring = null;
    private int numRules = 0;
    
    private static final Runtime s_runtime = Runtime.getRuntime();
    
    private int clusterType = 0;
    private int recordType = 0;
    private int counterForMemory;
    private String rsf;
    
    Set<String> debugRecords = new LinkedHashSet<String>();
    
    String killFile = null;
    
    boolean die = false;
    
    /**
     * This method is used to load a set of RefIDs into the debugRecords
     * @param filename the absolute filename
     */
    private void loadDebug(String filename) {
        String read, text;
        int count = 0;
        BufferedReader in = null;

        try {
            in = new BufferedReader(new FileReader(filename));
            while ((read = in.readLine()) != null) {
                if (!read.startsWith("!!")) {
                    text = read;
                    debugRecords.add(text);
                    count++;
                }
            }
            System.out.println(count + " Debug Elements loaded...");
        } catch (IOException ex) {
            Logger.getLogger(OysterMain.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } finally {
            try {
                if (in != null) {
                    in.close();
                }
            } catch (IOException ex) {
                Logger.getLogger(OysterMain.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
            }
        }
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.C6A9B594-31EE-5041-94B7-EFD3FEE73CE3]
    // </editor-fold>
    /**
     * Creates a new instance of <code>OysterMain</code>.
     */
    public OysterMain () {
        ruleFreq = new TreeMap<String, Long>();
        completeRuleFiring = new TreeMap<String, Long>();
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.BAFF9A85-CC96-FEAC-F3C6-91F12981F31B]
    // </editor-fold>
    /**
     * Creates a new instance of <code>OysterMain</code>.
     * @param repository the repository to be set
     * @param attributes the attributes to be set
     */
    public OysterMain (OysterIdentityRepository repository, OysterAttributes attributes) {
        this.repository = repository;
        this.attributes = attributes;
        ruleFreq = new TreeMap<String, Long>();
        completeRuleFiring = new TreeMap<String, Long>();
    }

    //==========================================================================
    //  ... Getter/Setters
    //==========================================================================
    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,regenBody=yes,id=DCE.D1F42EE7-0D9E-36A1-8902-CD2D80A4E05A]
    // </editor-fold>
    /**
     * Returns the <code>OysterAttributes</code> for this <code>OysterMain</code>.
     * @return the <code>OysterAttributes</code>.
     */
    public OysterAttributes getAttributes () {
        return attributes;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,regenBody=yes,id=DCE.F0F35579-A43E-F308-4018-2C1A0ED70C40]
    // </editor-fold>
    /**
     * Sets the <code>OysterAttributes</code> for this <code>OysterMain</code>.
     * @param attributes the <code>OysterAttributes</code> to be set.
     */
    public void setAttributes (OysterAttributes attributes) {
        this.attributes = attributes;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,regenBody=yes,id=DCE.E6F7A877-CD09-1192-76B5-AE9FB00F09A3]
    // </editor-fold>
    /**
     * Returns the <code>OysterEngine</code> for this <code>OysterMain</code>.
     * @return the <code>OysterEngine</code>.
     */
    public OysterEngine getEngine () {
        return engine;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,regenBody=yes,id=DCE.C6FE0F01-3B92-0B7E-614D-D16418434FF2]
    // </editor-fold>
    /**
     * Sets the <code>OysterEngine</code> for this <code>OysterMain</code>.
     * @param engine the <code>OysterEngine</code> to be set.
     */
    public void setEngine (OysterEngine engine) {
        this.engine = engine;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,regenBody=yes,id=DCE.4DAA17F1-A256-BA71-8F04-51A412731B4F]
    // </editor-fold>
    /**
     * Returns the <code>OysterIdentityRepository</code> for this <code>OysterMain</code>.
     * @return the <code>OysterIdentityRepository</code>.
     */
    public OysterIdentityRepository getRepository () {
        return repository;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,regenBody=yes,id=DCE.59349A8D-B259-8C28-852A-27134A2608B3]
    // </editor-fold>
    /**
     * Sets the <code>OysterIdentityRepository</code> for this <code>OysterMain</code>.
     * @param repository the <code>OysterIdentityRepository</code> to be set.
     */
    public void setRepository (OysterIdentityRepository repository) {
        this.repository = repository;
    }

    public Index getIndex() {
        return index;
    }

    public void setIndex(Index aIndex) {
        index = aIndex;
    }

    public EntityMap getEntityMap() {
        return entityMap;
    }

    public void setEntityMap(EntityMap aEntityMap) {
        entityMap = aEntityMap;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.D266CD1A-703B-0782-751D-A0A06CFF620E]
    // </editor-fold>
    /**
     * Returns the <code>OysterRunScript</code> for this <code>OysterMain</code>.
     * @return the <code>OysterRunScript</code>.
     */
    public OysterRunScript getRunScript () {
        return this.runScript;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.3F827DC2-3C1A-B9E8-4F23-AEA7AD61702F]
    // </editor-fold>
    /**
     * Sets the <code>OysterRunScript</code> for this <code>OysterMain</code>.
     * @param runScript the <code>OysterRunScript</code> to be set.
     */
    public void setRunScript (OysterRunScript runScript) {
        this.runScript = runScript;
    }

    /**
     * Returns the Sources for this <code>OysterMain</code>.
     * @return the Sources.
     */
    public TreeMap<Integer, OysterReferenceSource> getSources() {
        return sources;
    }

    /**
     * Sets the Sources for this <code>OysterMain</code>.
     * @param sources the Sources to be set.
     */
    public void setSources(TreeMap<Integer, OysterReferenceSource> sources) {
        this.sources = sources;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.7D05AECF-E050-9EE5-A559-CC7B01AEC73F]
    // </editor-fold>
    /**
     * Returns the version for this <code>OysterMain</code>.
     * @return the version.
     */
    public String getVersion () {
        return version;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.DCB416C2-ADB6-C0D3-C444-00AC9582F81F]
    // </editor-fold>
    /**
     * Sets the version for this <code>OysterMain</code>.
     * @param version the version to be set.
     */
    public void setVersion (String version) {
        this.version = version;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.E8BCAA0F-E2B1-33BB-14C3-27FAAC80755B]
    // </editor-fold>
    /**
     * Returns the class name for this <code>OysterMain</code>.
     * @return getClass().getName()
     */
    public String getClassName () {
        return getClass().getName();
    }

    /**
     * 
     * @param ade
     * @return
     */
    private String getRunScriptName(boolean ade) {
        StringBuilder run = new StringBuilder(100);
        int c;
        System.out.println("Please input the name of the runScript:");

        if (!ade) {
            run.append("Z:\\Oyster\\");
        }

        try {
            File f;
            do{
                do{
                    c = System.in.read();
                    run.append((char) c);
                } while (c != 10 && c != 13);

                run.replace(0, run.length(), run.toString().replaceAll("[\n\r]", ""));

                // check to see if the file exist
                f = new File(run.toString());

                if (!f.exists()){
                    String file = f.getName();
                    String dir = f.getParent();

                    if (file == null || file.trim().equals("")) {
                        file = "<blank>";
                    }
                    if (dir == null || dir.trim().equals("")) {
                        dir = "<blank>";
                    }

                    if (dir.equals("<blank>") && file.equals("<blank>")) {
                        System.out.println("No filename entered.");
                    } else {
                        System.out.println("The RunScript: " + file + " does not exist in the directory: " + dir);
                    }
                    System.out.println();
                    System.out.println("Please re-enter the correct RunScript:");

                } else{
                    System.out.println("Opening " + f.getAbsolutePath());
                    System.out.println();
                }
            } while(!f.exists());
        } catch (IOException ex) {
            Logger.getLogger(OysterMain.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return run.toString();
    }

    /**
     * Returns the formated log file if no log file is given in the command-line
     * arguments or in the RunScript.
     * @param file the runscript filename
     * @return the formated log filename
     */
    public String getLogPath(String file){
        String result;
        File f = new File(file);
        result = f.getAbsolutePath();

        // remove the extension
        int dot;
        if ((dot = result.lastIndexOf(".")) != -1){
            result = result.substring(0, dot);
            
            // does this contain the formatted log String?
            if (result.indexOf("%g") == -1) {
                result += "_%g";
            }
            
            // now add the log extension
            result += ".log";
        } else {
            result += "_%g.log";
        }

        return result;
    }

    /**
     * Returns the Start Time for this <code>OysterMain</code>.
     * @return startTime
     */
    public String getStartTime() {
        return startTime;
    }

    /**
     * Returns the Stop Time for this <code>OysterMain</code>.
     * @return stopTime
     */
    public String getStopTime() {
        return stopTime;
    }

    /**
     * Returns the Total Records for this <code>OysterMain</code>.
     * @return totalRecords
     */
    public long getTotalRecords() {
        return totalRecords;
    }

    /**
     * Returns the total RSwoosh iterations for this <code>OysterMain</code>.
     * @return totalRSwooshs
     */
    public long getTotalRSwooshs() {
        return totalRSwooshs;
    }
    
    /**
     * Returns the number of groups for this <code>OysterMain</code>.
     * @return groups
     */
    public long getGroups() {
        return groups;
    }
    
    /**
     * Returns the Maximun Group Size for this <code>OysterMain</code>.
     * @return maxGroupSize
     */
    public long getMaxGroupSize() {
        return maxGroupSize;
    }

    /**
     * Returns the Minimun Group Size for this <code>OysterMain</code>.
     * @return minGroupSize
     */
    public long getMinGroupSize() {
        return minGroupSize;
    }

    /**
     * Returns the Minimun Group Size greater 1 for this <code>OysterMain</code>.
     * @return minGroupSizeGT1
     */
    public long getMinGroupSizeGT1() {
        return minGroupSizeGT1;
    }

    /**
     * Returns the Cluster Frequency for this <code>OysterMain</code>.
     * @return clusterFreq
     */
    public Map<Long, Long> getClusterFreq() {
        return clusterFreq;
    }
    
    /**
     * Returns the Average Cluster Group for this <code>OysterMain</code>.
     * @return avgClusterGroup
     */
    public long getAvgClusterGroup() {
        return avgClusterGroup;
    }

    /**
     * Returns the Average Cluster Count for this <code>OysterMain</code>.
     * @return avgClusterCount
     */
    public long getAvgClusterCount() {
        return avgClusterCount;
    }

    /**
     * Returns the Average Cluster Size for this <code>OysterMain</code>.
     * @return avgClusterSize
     */
    public double getAvgClusterSize() {
        return avgClusterSize;
    }

    /**
     * Returns the Duplication Rate for this <code>OysterMain</code>.
     * @return duplicationRate
     */
    public double getDuplicationRate() {
        return duplicationRate;
    }

    /**
     * Returns the Rule Frequency for this <code>OysterMain</code>.
     * @return ruleFreq
     */
    public Map<String, Long> getRuleFreq() {
        return ruleFreq;
    }
    
    /**
     * Returns the Number Rules for this <code>OysterMain</code>.
     * @return numRules
     */
    public int getNumRules() {
        return numRules;
    }

    /**
     * This method returns the next available Modification ID based on the input
     * mods. This is basically just an incremental number.
     * @param mods the previous modification if any exist.
     * @return
     */
    public String nextMID(TreeMap<String, ModificationRecord> mods) {
        int number = 0;
        for (Iterator<Entry<String, ModificationRecord>> it = mods.entrySet().iterator(); it.hasNext();){
            Entry<String, ModificationRecord> entry = it.next();
            ModificationRecord mr = entry.getValue();
            number = Math.max(number, Integer.parseInt(mr.getId()));
        }
        number++;

        String result = String.valueOf(number);
        // pad with zero's
//        while (result.length() < 7){
//            result = "0" + result;
//        }

        return result;
    }
    
    //==========================================================================
    //  ... Time Methods
    //==========================================================================
    /**
     * Returns the system time at a specific point in time
     * @return the time as a string
     */
    private String now(){
        String result;
        /* Get system time & date */
        String DATE_FORMAT = "yyyy-MM-dd HH.mm.ss";
        java.text.SimpleDateFormat sdf = new java.text.SimpleDateFormat(DATE_FORMAT);
        sdf.setTimeZone(TimeZone.getDefault());
        Calendar cal = Calendar.getInstance(TimeZone.getDefault());

        result = sdf.format(cal.getTime());
        return result;
    }

    /**
     * Returns a date for the formated string
     * @param date the string date
     * @return the date
     */
    private Date toDate(String date){
        Date result = null;
        try {
            /* Get system time & date */
            String DATE_FORMAT = "yyyy-MM-dd HH.mm.ss";
            java.text.SimpleDateFormat sdf = new java.text.SimpleDateFormat(DATE_FORMAT);
            sdf.setTimeZone(TimeZone.getDefault());

            result = sdf.parse(date);
        } catch (ParseException ex) {
            Logger.getLogger(OysterMain.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return result;
    }

    /**
     * This method determines how much time has elapsed from the start time until
     * the stop time.
     * @return the elapsed amount of time as a string
     */
    private String elapsedTime(){
        String result;
        GregorianCalendar gc1 = new GregorianCalendar();
        GregorianCalendar gc2 = new GregorianCalendar();

        gc1.setTime(toDate(startTime));
        gc2.setTime(toDate(stopTime));

        // the above two dates are one second apart
        Date d1 = gc1.getTime();
        Date d2 = gc2.getTime();
        long l1 = d1.getTime();
        long l2 = d2.getTime();
        long difference = l2 - l1;
        long timeInSeconds = difference / 1000;

        long hours, minutes, seconds;
        hours = timeInSeconds / 3600;
        timeInSeconds = timeInSeconds - (hours * 3600);
        minutes = timeInSeconds / 60;
        timeInSeconds = timeInSeconds - (minutes * 60);
        seconds = timeInSeconds;
        result = hours + " hour(s) " + minutes + " minute(s) " + seconds + " second(s)";
        return result;
    }

    private long elapsedSecs(String start, String stop){
        GregorianCalendar gc1 = new GregorianCalendar();
        GregorianCalendar gc2 = new GregorianCalendar();

        gc1.setTime(toDate(start));
        gc2.setTime(toDate(stop));

        // the above two dates are one second apart
        Date d1 = gc1.getTime();
        Date d2 = gc2.getTime();
        long l1 = d1.getTime();
        long l2 = d2.getTime();
        long difference = l2 - l1;
        long timeInSeconds = difference / 1000;

        return timeInSeconds;
    }
    
    //==========================================================================
    //  ... Initialization/Validation Methods
    //==========================================================================
    /**
     * This method takes the Comparators found in the input OysterAttributes.xml
     * file and instantiates each one. If a valid Comparator can not be found an
     * <code>OysterCompareDefault</code> is instantiates in its place.
     */
    private void initializeComparators() {
        logger.severe("Initializing Comparators...");
        System.out.println(System.getProperty("line.separator") + "Initializing Comparators...");

        for (Iterator<OysterAttribute> it = getAttributes().getAttrComp().keySet().iterator(); it.hasNext();){
            OysterAttribute oa = it.next();
            OysterComparator oc;

            try {
                Class comp = Class.forName(oa.getAlgorithm());
                oc = (OysterComparator) comp.newInstance();
            } catch (Exception ex) {
                logger.severe(ex.getMessage());
                StringBuilder sb = new StringBuilder(100);
                sb.append("Unknown or Invalid Comparator Class: ")
                  .append(oa.getAlgorithm())
                  .append(System.getProperty("line.separator"));
                sb.append("Initializing OysterCompareDefault for ")
                  .append(oa.getName());
                logger.severe(sb.toString());
                oc = new OysterCompareDefault();
            }

            StringBuilder sb = new StringBuilder(250);
            sb.append(oa.getName())
              .append("\t")
              .append(oc.getAllAvailableMatchCodes())
               .append(System.getProperty("line.separator"));
            logger.severe(sb.toString());
            System.out.println(sb.toString());

            getAttributes().getAttrComp().put(oa, oc);
        }
        logger.severe("");
        System.out.println();
    }

    /**
     * This method finds the Least Common Rules Denominator for set if rules
     * found in a OysterAttribute. This is done by looking for the rules with
     * the high precedence that occur only once within a group of records.
     * @param identityRules the input rules to be searched.
     * @return a list of elements the MUST exist within a Reference.
     */
    public Map<Integer, ArrayList<String>> lcrd(ArrayList<OysterRule> identityRules) {
        int count = 0;
        Map<Integer, ArrayList<String>> lcd = new LinkedHashMap<Integer, ArrayList<String>>();
        Map <Integer, Map<String, ArrayList<String>>> temp = new LinkedHashMap <Integer, Map<String, ArrayList<String>>>();

//        System.out.println("Identity Rules: " + identityRules);
        
        
        //FIXME: Need to ba able to create this with new RuleTerm using either the item or second item
        Iterator<OysterRule> it = identityRules.iterator();
        do{
            OysterRule or = it.next();

            // check to see if this rule contains the exact same Term Items as a previous rule
            boolean found = false;
            int key2 = -1;
            for (Iterator<Integer> it2 = temp.keySet().iterator(); it2.hasNext();){
                key2 = it2.next();
                Map<String, ArrayList<String>> m = temp.get(key2);
                found = true;

                if (m.size() == or.getTermList().size()) {
                    for (Iterator<String> it3 = m.keySet().iterator(); it3.hasNext();) {
                        String attribute = it3.next();

                        found = false;
                        for (Iterator<RuleTerm> rtIT = or.getTermList().iterator(); rtIT.hasNext();){
                            RuleTerm rt = rtIT.next();
                            if (rt.getItem().equals(attribute)){
                                found = true;
                                break;
                            }
                        }

                        if (!found) {
                            found = false;
                            break;
                        }
                    }

                    if (!found) {
                        break;
                    }
                } else {
                    found = false;
                }
            }

            Map<String, ArrayList<String>> m;
            if (found && count != 0){
                m = temp.get(key2);
            } else {
                m = new LinkedHashMap<String, ArrayList<String>>();
            }

            for (Iterator<RuleTerm> it2 = or.getTermList().iterator(); it2.hasNext();){
                RuleTerm rt = it2.next();

                ArrayList<String> al = m.get(rt.getItem());

                if (al == null) {
                    al = new ArrayList<String>();
                }

                if (!al.contains(rt.getMatchResult())) {
                    al.add(rt.getMatchResult());
                }

                m.put(rt.getItem(), al);
            }

            if (found && count != 0){
                temp.put(key2, m);
            } else {
                temp.put(count++, m);
            }

        } while ( it.hasNext());

//        System.out.println("Temp = " + temp);
        
        for (Iterator<Integer> it2 = temp.keySet().iterator(); it2.hasNext();) {
            int key = it2.next();
            Map<String, ArrayList<String>> m = temp.get(key);

            // I only care about single entries that are EXACT
            for (Iterator<String> it3 = m.keySet().iterator(); it3.hasNext();) {
                String key3 = it3.next();
                ArrayList<String> al = m.get(key3);

                if (al.size() == 1 && (al.get(0).equalsIgnoreCase("Exact") || al.get(0).equalsIgnoreCase("Exact_Ignore_Case"))) {
                    ArrayList<String> value = lcd.get(key);
                    if (value == null) {
                        value = new ArrayList<String>();
                    }

                    value.add(key3);
                    lcd.put(key, value);
                }
            }
        }
//        System.out.println("LCRD All = " + lcd);
        // lastly, check to see if a filter is a subset of another filter if it
        // is remove the super filter
        for (int i = 0; i < count; i++){
            ArrayList<String> ali = lcd.get(i);

            for (int j = 0; j < count; j++){
                ArrayList<String> alj = lcd.get(j);

                if (i != j && ali != null && alj != null && ali.size() <= alj.size()){
                    if (alj.containsAll(ali)){
                        lcd.remove(j);
                    }
                }
            }
        }
//        System.out.println("LCRD Final = " + lcd);
        return lcd;
    }

    /**
     * This method opens the apporpriate output for each ER mode.
     * <table>
     * <th><td></td><td>OysterIdentityRepository</td><td>Link Output</td><td>Repository Output</td></th>
     * <tr><td>RUNMODE_MERGE_PURGE</td><td></td><td>x</td><td></td></tr>
     * <tr><td>RUNMODE_IDENT_RESOLVE</td><td>x</td><td>x</td></tr>
     * <tr><td>RUNMODE_IDENT_CAPTURE</td><td>x</td><td>x</td><td>x</td></tr>
     * <tr><td>RUNMODE_IDENT_UPDATE</td><td>x</td><td>x	x</td></tr>
     * <tr><td>RUNMODE_ASSERT_REF2REF</td><td>x</td><td>x</td><td>x</td></tr>
     * <tr><td>RUNMODE_ASSERT_REF2STR</td><td>x</td><td>x</td><td>x</td></tr>
     * <tr><td>RUNMODE_ASSERT_STR2STR</td><td>x</td><td></td><td>x</td></tr>
     * <tr><td>RUNMODE_ASSERT_SPLIT_STR</td><td>x</td><td></td><td>x</td></tr>
     * </table>
     * @param keepPreviousDBTable
     * @return
     */
    public boolean openOysterOutputs(boolean keepPreviousDBTable) {
        boolean flag = false;
        String runmode = runScript.getRunMode();
        try {
            //==================================================================
            // Create a single instance of OysterIdentityRepository
            //==================================================================
            if (runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_RESOLVE) || 
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_CAPTURE) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_UPDATE) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_REF2REF) || 
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_REF2STR) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_STR2STR) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_SPLIT_STR)) {
                if (runScript.getIdentityInputType().equalsIgnoreCase("None")) {
                    setRepository(new OysterIdentityRepository(logger, attributes, runScript.getSecurityHash(), recordType));
                    repository.setEntityMap(entityMap);
                    repository.setValueIndex(index);
                    repository.setLinkMap(new HashMap<String, String>());
                    repository.setPassThruAttributes(passThruAttributes);
                    repository.setMid("1");
                    sourceNames = new LinkedHashSet<String>();
                } else if (runScript.getIdentityInputType().equalsIgnoreCase("TextFile")) {
                    setRepository(new OysterIdentityRepository(logger, attributes, runScript.getSecurityHash(), recordType));

                    repository.setEntityMap(entityMap);
                    repository.setValueIndex(index);
                    repository.setLinkMap(new HashMap<String, String>());
                    repository.setPassThruAttributes(passThruAttributes);

                    StringBuilder sb = new StringBuilder(250);
                    sb.append("Identity Input Type: ")
                      .append(runScript.getIdentityInputType())
                      .append(System.getProperty("line.separator"));
                    sb.append("Identity Input: ")
                      .append(runScript.getIdentityInputLocation())
                      .append(System.getProperty("line.separator"));
                    logger.severe(sb.toString());
                    repository.load(runScript.getIdentityInputLocation(), keepPreviousDBTable, runScript.isIdentityOutputTrace());
                    sourceNames = repository.getSourceNames();
                    
                    // determine the next mid number
                    repository.setMid(nextMID(repository.getMods()));
                } else if (runScript.getIdentityInputType().equalsIgnoreCase("Database")) {
                    StringBuilder sb = new StringBuilder(250);
                    sb.append("Identity Input Type: ")
                      .append(runScript.getIdentityInputType())
                      .append(System.getProperty("line.separator"));
                    sb.append("Identity Input: ")
                      .append(runScript.getIdentityInputLocation())
                      .append(System.getProperty("line.separator"));
                    logger.severe(sb.toString());
                    // repository.load(runScript.getIdentityInputLocation(), runScript.isLinkOutputAppend());
                    // sourceNames = repository.getSourceNames();
                    sourceNames = new LinkedHashSet<String>();
                } else {
                    return false;
                }
            } else {
                setRepository(new OysterIdentityRepository(logger, attributes, runScript.getSecurityHash(), recordType));
                repository.setEntityMap(entityMap);
                repository.setValueIndex(index);
                repository.setLinkMap(new HashMap<String, String>());
                repository.setPassThruAttributes(passThruAttributes);
                sourceNames = new LinkedHashSet<String>();
            }
            repository.setDebug(runScript.isDebug());
            repository.setSlidingWindow(runScript.getSlidingWindow());

            //==================================================================
            // Set Link Output
            //==================================================================
            if (runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_MERGE_PURGE) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_RECORD_LINKAGE) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_CAPTURE) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_RESOLVE) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_UPDATE) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_REF2REF) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_REF2STR)) {
                if (runScript.getLinkOutputType().equalsIgnoreCase("TextFile")) {
                    StringBuilder sb = new StringBuilder(250);
                    sb.append("Link Output Type: ")
                      .append(runScript.getLinkOutputType())
                      .append(System.getProperty("line.separator"));
                    sb.append("Link Output: ")
                      .append(runScript.getLinkOutputLocation())
                      .append(System.getProperty("line.separator"));
                    logger.severe(sb.toString());
                    repository.setLinkMapWriter(new PrintWriter(new OutputStreamWriter(new FileOutputStream(runScript.getLinkOutputLocation()), "UTF8")));
                } else if (runScript.getLinkOutputType().equalsIgnoreCase("Database")) {
                    StringBuilder sb = new StringBuilder(250);
                    sb.append("Link Output Type: ")
                      .append(runScript.getLinkOutputType())
                      .append(System.getProperty("line.separator"));
                    sb.append("Link Output: ")
                      .append(runScript.getLinkOutputLocation())
                      .append(System.getProperty("line.separator"));
                    logger.severe(sb.toString());

                    repository.setLinkDatabaseWriter(new OysterDatabaseWriter(runScript.getLinkOutputLocation(),
                            runScript.getLinkOutputCType(),
                            runScript.getLinkOutputServer(),
                            runScript.getLinkOutputPort(),
                            runScript.getLinkOutputSID(),
                            runScript.getLinkOutputUserID(),
                            runScript.getLinkOutputPasswd()));
                    if (repository.getLinkDatabaseWriter().isConnected()) {
                        // does the table exist?
                        if (repository.getLinkDatabaseWriter().doesTableExist()) {
                            if (true) {
                                repository.getLinkDatabaseWriter().deleteData();
                            }
                        } else {
                            if (!repository.getLinkDatabaseWriter().createLinkTable()) {
                                sb = new StringBuilder(250);
                                sb.append("Unable to create Table")
                                  .append(getRepository().getLinkDatabaseWriter().getTableName())
                                  .append(System.getProperty("line.separator"));
                                logger.severe(sb.toString());
                                return false;
                            }
                        }
                        // create the SQL statement
                        repository.getLinkDatabaseWriter().createLinkTablePreparedStatement();
                    }
                } else {
                    return false;
                }
            }

            //==================================================================
            // Set Repository Output
            //==================================================================
            if (runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_CAPTURE) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_UPDATE) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_REF2REF) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_REF2STR) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_STR2STR) ||
                    runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_SPLIT_STR)) {
                if (runScript.getIdentityOutputType().equalsIgnoreCase("None")) {
                    
                } else if (runScript.getIdentityOutputType().equalsIgnoreCase("TextFile")) {
                    StringBuilder sb = new StringBuilder(250);
                    sb.append("Identity Output Type: ")
                      .append(runScript.getIdentityOutputType())
                      .append(System.getProperty("line.separator"));
                    sb.append("Identity Output: ")
                      .append(runScript.getIdentityOutputLocation())
                      .append(System.getProperty("line.separator"));
                    logger.severe(sb.toString());
                    repository.setRepositoryWriter(new PrintWriter(new OutputStreamWriter(new FileOutputStream(runScript.getIdentityOutputLocation()), "UTF8")));
                    repository.setTraceOn(runScript.isIdentityOutputTrace());
                } else if (runScript.getIdentityOutputType().equalsIgnoreCase("Database")) {
                    StringBuilder sb = new StringBuilder(250);
                    sb.append("Identity Output Type: ")
                      .append(runScript.getIdentityOutputType())
                      .append(System.getProperty("line.separator"));
                    sb.append("Identity Output: ")
                      .append(runScript.getIdentityOutputLocation())
                      .append(System.getProperty("line.separator"));
                    logger.severe(sb.toString());
                    logger.severe("");
                    repository.setTraceOn(runScript.isIdentityOutputTrace());

//                repository.setIdentityDatabaseWriter(new OysterDatabaseWriter(runScript.getLinkOutputLocation(), 
//                runScript.getLinkOutputCType(), 
//                runScript.getLinkOutputServer(),
//                runScript.getLinkOutputPort(),
//                runScript.getLinkOutputSID(),
//                runScript.getLinkOutputUserID(),
//                runScript.getLinkOutputPasswd()));
                } else {
                    return false;
                }
            }

            //==================================================================
            // If DEBUG then set the debug files
            //==================================================================
            String temp;
            if (runScript.isDebug()) {
                File debug;
                if (runScript.getIdentityOutputLocation() != null && !runScript.getIdentityOutputLocation().equals("")) {
                    debug = new File(runScript.getIdentityOutputLocation());
                } else {
                    debug = new File(runScript.getLinkOutputLocation());
                }
                
                temp = debug.getParent() + System.getProperty("file.separator") + debug.getName().replaceAll("\\.[a-zA-Z]+", "");
                repository.setIndexWriter(new PrintWriter(new OutputStreamWriter(new FileOutputStream(temp + ".indx"), "UTF8")));
                repository.setEntityWriter(new PrintWriter(new OutputStreamWriter(new FileOutputStream(temp + ".emap"), "UTF8")));
            }
            
            //==================================================================
            // create the change report file
            //==================================================================
            if (repository.isTraceOn()) {
                File changeReport;
                if (runScript.getIdentityOutputLocation() != null && !runScript.getIdentityOutputLocation().equals("")) {
                    changeReport = new File(runScript.getIdentityOutputLocation());
                } else {
                    changeReport = new File(runScript.getLinkOutputLocation());
                }
        
                temp = changeReport.getParent() + System.getProperty("file.separator");
                repository.setChangeReportWriter(new PrintWriter(new OutputStreamWriter(new FileOutputStream(temp + "Identity Change Report.txt"), "UTF8")));
            
                // Changed per OYSTER Version 3.2 Requirements Requirement 2.3.4, Requirement 2.4.5, Requirement 2.5.7 & Requirement 2.5.7
                if (!runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_REF2REF) &&
                    !runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_REF2STR) &&
                    !runmode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_SPLIT_STR)) {
                    repository.setMergeMapWriter(new PrintWriter(new OutputStreamWriter(new FileOutputStream(temp + "Identity Merge Map.csv"), "UTF8")));
                } else {
                    repository.setMergeMapWriter(null);
                }
            }
            flag = true;
        } catch (FileNotFoundException ex) {
            Logger.getLogger(OysterMain.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch (UnsupportedEncodingException ex) {
            Logger.getLogger(OysterMain.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return flag;
    }

    /**
     * This method validates <code>OysterAttributes</code>. Each rule within
     * the IdentityRules must have a matching item name within the Attribute
     * section.
     * @param attributes the <code>OysterAttributes</code> to be validated.
     * @return true if the <code>OysterAttributes</code> has been validated,
     * otherwise false.
     */
    public boolean validateAttributes(OysterAttributes attributes) {
        boolean found = true;
        passThruAttributes = new HashSet<String>();

        // get a list of all the elements within the Reference Items
        ArrayList<String> al = new ArrayList<String>();
        for (Iterator<OysterAttribute> it = attributes.getAttrComp().keySet().iterator(); it.hasNext();) {
            OysterAttribute oa = it.next();

            if (!al.contains(oa.getName())) {
                al.add(oa.getName());
            }
            passThruAttributes.add(oa.getName());
        }

        for (Iterator<OysterRule> it = attributes.getIdentityRules().iterator(); it.hasNext();) {
            OysterRule or = it.next();

            for (Iterator<RuleTerm> it2 = or.getTermList().iterator(); it2.hasNext();) {
                RuleTerm rt = it2.next();

                if (!al.contains(rt.getItem())) {
                    System.out.println("##ERROR: Rule Item: " + rt.getItem() + " not an Attribute");
                    found = false;
                    break;
                }

                // check the compareTo elements
                if (rt.getCompareTo() != null && !rt.getCompareTo().isEmpty()) {
                    for (Iterator<String> it3 = rt.getCompareTo().iterator(); it3.hasNext();) {
                        String compareTo = it3.next();

                        if (!al.contains(compareTo)) {
                            System.out.println("##ERROR: CompareTo: " + compareTo + " not an Attribute");
                            found = false;
                            break;
                        }
                    }
                }

                if (!found) {
                    break;
                }

                // remove all rule items from the list of possible attributes
                if (passThruAttributes.contains(rt.getItem())) {
                    passThruAttributes.remove(rt.getItem());
                }
            }
        }

        ///System.out.println("or : " + v);

        //System.out.println();
        return found;
    }

    /**
     * This method validates <code>OysterReferenceSource</code> against the
     * <code>OysterAttributes</code>. Each item in the ReferenceItems section must
     * have a matching Attribute in the Oyster Attribute or it must use the @Skip
     * keyword.
     * @param source the <code>OysterReferenceSource</code> to be validated.
     * @param attributes the <code>OysterAttributes</code> to be validated against.
     * @return true if the <code>OysterReferenceSource</code> has been validated,
     * otherwise false.
     */
    public boolean validateReferences(OysterReferenceSource source, OysterAttributes attributes) {
        boolean found = false;
        ReferenceItem ri = null;
        Map<OysterAttribute, OysterComparator> attrComp = attributes.getAttrComp();

        if (runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_STR2STR)) {
            for (Iterator<ReferenceItem> it = source.getReferenceItems().iterator(); it.hasNext();) {
                ri = it.next();
                found = false;
                if (ri.getAttribute().equalsIgnoreCase(OysterKeywords.ASSERT_STR_TO_STR)) {
                    // check to be sure that the metadata is updated to include
                    // this attribute
                    if (ClusterRecord.getMetadata().get(OysterKeywords.ASSERT_STR_TO_STR) == null) {
                        ClusterRecord temp = new ClusterRecordSet(recordType);
                        temp.updateMetaData(OysterKeywords.ASSERT_STR_TO_STR);
                    }
                    found = true;
                } else if (ri.getAttribute().equalsIgnoreCase(OysterKeywords.OID)) {
                    if (ClusterRecord.getMetadata().get(OysterKeywords.OID) == null) {
                        ClusterRecord temp = new ClusterRecordSet(recordType);
                        temp.updateMetaData(OysterKeywords.OID);
                    }
                    found = true;
                } else if (ri.getAttribute().equalsIgnoreCase(OysterKeywords.REFID)) {
                    found = true;
                } else {
                    break;
                }
            }
        } else if (runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_SPLIT_STR)) {
            for (Iterator<ReferenceItem> it = source.getReferenceItems().iterator(); it.hasNext();) {
                ri = it.next();
                found = false;
                if (ri.getAttribute().equalsIgnoreCase(OysterKeywords.ASSERT_SPLIT_STR)) {
                    // check to be sure that the metadata is updated to include
                    // this attribute
                    if (ClusterRecord.getMetadata().get(OysterKeywords.ASSERT_SPLIT_STR) == null) {
                        ClusterRecord temp = new ClusterRecordSet(recordType);
                        temp.updateMetaData(OysterKeywords.ASSERT_SPLIT_STR);
                    }
                    found = true;
                } else if (ri.getAttribute().equalsIgnoreCase(OysterKeywords.OID)) {
                    if (ClusterRecord.getMetadata().get(OysterKeywords.OID) == null) {
                        ClusterRecord temp = new ClusterRecordSet(recordType);
                        temp.updateMetaData(OysterKeywords.OID);
                    }
                    found = true;
                } else if (ri.getAttribute().equalsIgnoreCase(OysterKeywords.RID)) {
                    if (ClusterRecord.getMetadata().get(OysterKeywords.RID) == null) {
                        ClusterRecord temp = new ClusterRecordSet(recordType);
                        temp.updateMetaData(OysterKeywords.RID);
                    }
                    found = true;
                } else if (ri.getAttribute().equalsIgnoreCase(OysterKeywords.REFID)) {
                    found = true;
                } else {
                    break;
                }
            }
        } else {
            // Cycle thruough the ReferenceItems and check it against the Attributes
            for (Iterator<ReferenceItem> it = source.getReferenceItems().iterator(); it.hasNext();) {
                ri = it.next();
                found = false;

                for (Iterator<OysterAttribute> it2 = attrComp.keySet().iterator(); it2.hasNext();) {
                    OysterAttribute oa = it2.next();
                    /*System.out.println("oa : " + oa.getName());
                    System.out.println("ri : " + ri.getAttribute());
                    System.out.println();*/

                    if (oa.getName().equalsIgnoreCase(ri.getAttribute())) {
                        found = true;
                        break;
                    } else if (ri.getAttribute().equalsIgnoreCase(OysterKeywords.REFID)) {
                        found = true;
                        break;
                    } else if (ri.getAttribute().equalsIgnoreCase(OysterKeywords.SKIP)) {
                        found = true;
                        break;
                    } else if (ri.getAttribute().equalsIgnoreCase(OysterKeywords.ASSERT_REF_TO_REF)) {
                        // check to be sure that the metadata is updated to include
                        // this attribute
                        if (ClusterRecord.getMetadata().get(OysterKeywords.ASSERT_REF_TO_REF) == null) {
                            ClusterRecord temp = new ClusterRecordSet(recordType);
                            temp.updateMetaData(OysterKeywords.ASSERT_REF_TO_REF);
                        }
                        found = true;
                        break;
                    } else if (ri.getAttribute().equalsIgnoreCase(OysterKeywords.ASSERT_REF_TO_STR)) {
                        // check to be sure that the metadata is updated to include
                        // this attribute
                        if (ClusterRecord.getMetadata().get(OysterKeywords.ASSERT_REF_TO_STR) == null) {
                            ClusterRecord temp = new ClusterRecordSet(recordType);
                            temp.updateMetaData(OysterKeywords.ASSERT_REF_TO_STR);
                        }
                        found = true;
                        break;
                    }
                }

                if (!found) {
                    break;
                }
            }
        }
        
        if (!found) {
            StringBuilder sb = new StringBuilder(100);
            sb.append("##ERROR: Reference Item: ")
              .append(ri.getAttribute())
              .append(" not an Attribute")
              .append(System.getProperty("line.separator"));
            logger.severe(sb.toString());
            System.out.println(sb.toString());
        }
        
        return found;
    }

    /**
     * This method validates that the match code for a rule item is in fact
     * available from the associated Comparator.
     *
     * @param attributes the list of Identity Rules to be validated
     * @return true if the MatchCodes have been validated, otherwise false
     */
    public boolean validateRuleMatchCodes(OysterAttributes attributes) {
        boolean flag = true;
        ArrayList<OysterRule> identityRules = attributes.getIdentityRules();
        numRules = identityRules.size();
        
        for (Iterator<OysterRule> it = identityRules.iterator(); it.hasNext();){
            OysterRule or = it.next();

            for (Iterator<RuleTerm> it2 = or.getTermList().iterator(); it2.hasNext();){
                RuleTerm rt = it2.next();
                String matchCode = rt.getMatchResult();
                
                // handle function call like match codes
                int begin;
                if ((begin = matchCode.indexOf("(")) != -1){
                    matchCode = matchCode.substring(0, begin);
                }
                
                OysterComparator oc = attributes.getComparator(rt.getItem());

                if (!oc.isMatchCode(matchCode.toUpperCase(Locale.US))){
                    StringBuilder sb = new StringBuilder(150);
                    sb.append("##ERROR: MatchCode: ")
                      .append(matchCode)
                      .append(" is not available for the ")
                      .append(oc.toString())
                      .append(" Comparator.")
                      .append(System.getProperty("line.separator"));
                    logger.severe(sb.toString());
                    System.out.println(sb.toString());
                    
                    flag = false;
                }
            }
        }
        return flag;
    }

    /**
     * This method validates that the RunScript.
     * @param rsFile the RunScript filename
     * @return true if the names match, otherwise false
     */
    public boolean validateRunScript(String rsFile) {
        boolean result = false, name = false, mode = false, io = false;
        try {
            // Validate the RunScript Name
            File f = new File(rsFile);
            String fileName = f.getName();

            // remove the extension
            int end;
            if ((end = fileName.lastIndexOf(".")) != -1){
                fileName = fileName.substring(0, end);
            }

            if (fileName.equalsIgnoreCase(runScript.getName())) {
                name = true;
            }
            
            // validate that runmode exist and is a vaild mode
            String runMode = runScript.getRunMode();
            if (runMode != null && !runMode.trim().equals("")){
                if (runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_MERGE_PURGE) ||
                    runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_RECORD_LINKAGE) ||
                    runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_CAPTURE) ||
                    runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_RESOLVE) ||
                    runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_UPDATE) ||
                    runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_REF2REF) ||
                    runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_REF2STR) ||
                    runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_STR2STR) ||
                    runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_SPLIT_STR)) {
                    mode = true;
                }
            } else {
                StringBuilder sb = new StringBuilder(150);
                sb.append("##ERROR: ")
                  .append(runScript.getRunMode())
                  .append(" invalid RunMode.");
                logger.severe(sb.toString());
            }
            
            // now validate the RunScript I/O
            if (mode && (runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_MERGE_PURGE) ||
                         runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_RECORD_LINKAGE))){
                if (runScript.getAttributeLocation()      != null && 
                    (runScript.getIdentityInputLocation() == null ||
                     runScript.getIdentityInputLocation().equals("") ||
                     runScript.getIdentityInputType().equalsIgnoreCase("None")) && 
                    (runScript.getIdentityOutputLocation() == null ||
                     runScript.getIdentityOutputLocation().equals("") ||
                     runScript.getIdentityOutputType().equalsIgnoreCase("None")) && 
                    runScript.getLinkOutputLocation()     != null && 
                    runScript.getAssertionInputLocation() == null && 
                    runScript.getSources()                != null) {
                    io = true;
                }
            } else if (mode && runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_CAPTURE)){
                if (runScript.getAttributeLocation()      != null && 
                    (runScript.getIdentityInputLocation() == null ||
                     runScript.getIdentityInputLocation().equals("") ||
                     runScript.getIdentityInputType().equalsIgnoreCase("None")) && 
                    runScript.getIdentityOutputLocation() != null && 
                    runScript.getLinkOutputLocation()     != null && 
                    runScript.getAssertionInputLocation() == null && 
                    runScript.getSources()                != null) {
                    io = true;
                }
            } else if (mode && runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_RESOLVE)){
                if (runScript.getAttributeLocation()      != null && 
                    runScript.getIdentityInputLocation()  != null && 
                    (runScript.getIdentityOutputLocation() == null ||
                     runScript.getIdentityOutputLocation().equals("") ||
                     runScript.getIdentityOutputType().equalsIgnoreCase("None")) && 
                    runScript.getLinkOutputLocation()     != null && 
                    runScript.getAssertionInputLocation() == null && 
                    runScript.getSources()                != null) {
                     io = true;
                 }
            } else if (mode && runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_UPDATE)){
                if (runScript.getAttributeLocation()      != null && 
                    runScript.getIdentityInputLocation()  != null && 
                    runScript.getIdentityOutputLocation() != null && 
                    runScript.getLinkOutputLocation()     != null && 
                    runScript.getAssertionInputLocation() == null && 
                    runScript.getSources()                != null) {
                    io = true;
                }
            } else if (mode && runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_REF2REF)){
                if (runScript.getAttributeLocation()      != null && 
                    runScript.getIdentityInputLocation()  != null && 
                    runScript.getIdentityOutputLocation() != null && 
                    runScript.getLinkOutputLocation()     != null && 
                    runScript.getAssertionInputLocation() != null && 
                    runScript.getSources()                == null) {
                    io = true;
                }
            } else if (mode && runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_REF2STR)){
                if (runScript.getAttributeLocation()      != null && 
                    runScript.getIdentityInputLocation()  != null && 
                    runScript.getIdentityOutputLocation() != null && 
                    runScript.getLinkOutputLocation()     != null && 
                    runScript.getAssertionInputLocation() != null && 
                    runScript.getSources()                == null) {
                    io = true;
                }
            } else if (mode && runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_STR2STR)){
                if (runScript.getAttributeLocation()      != null && 
                    runScript.getIdentityInputLocation()  != null && 
                    runScript.getIdentityOutputLocation() != null && 
                    runScript.getLinkOutputLocation()     == null && 
                    runScript.getAssertionInputLocation() != null && 
                    runScript.getSources()                == null) {
                    io = true;
                }
            } else if (mode && runMode.equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_SPLIT_STR)){
                if (runScript.getAttributeLocation()      != null && 
                    runScript.getIdentityInputLocation()  != null && 
                    runScript.getIdentityOutputLocation() != null && 
                    runScript.getLinkOutputLocation()     == null && 
                    runScript.getAssertionInputLocation() != null && 
                    runScript.getSources()                == null) {
                    io = true;
                }
            } else {
                System.out.println("##ERROR: Invalid RunScript Mode.");
                logger.severe("##ERROR: Invalid RunScript Mode.");
            }
            
            if (!name){
                System.out.println("##ERROR: Invalid RunScript Name, does not match the external name.");
                logger.severe("##ERROR: Invalid RunScript Name, does not match the external name.");
            }
            
            if (!mode){
                StringBuilder sb = new StringBuilder(150);
                sb.append("##ERROR: UNKNOWN ")
                  .append(runScript.getRunMode())
                  .append(" Mode.");
                logger.severe(sb.toString());
                System.out.println(sb.toString());
            }
            
            if (!io){
                StringBuilder sb = new StringBuilder(150);
                sb.append("##ERROR: ")
                  .append(runScript.getRunMode())
                  .append(" Mode incorrectly configured.");
                logger.severe(sb.toString());
                System.out.println(sb.toString());
                logger.severe(runScript.getAttributeLocation());
                logger.severe(runScript.getIdentityInputLocation());
                logger.severe(runScript.getIdentityOutputLocation());
                logger.severe(runScript.getLinkOutputLocation());
                logger.severe(runScript.getAssertionInputLocation());
                logger.severe(runScript.getSources().toString());
            }
            
            if (name && mode && io){
                result = true;
            }
        } catch(RuntimeException ex){
            Logger.getLogger(OysterMain.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return result;
    }

    /**
     * This method check to ensure that the rule identifiers are unique.
     * @param attributes the list of Identity Rules to be validated
     * @return true if the rules numbering is unique, otherwise false
     */
    public boolean validateRuleNumbering(OysterAttributes attributes){
        boolean flag = true;
        Set<String> temp = new LinkedHashSet<String>();
        ArrayList<OysterRule> identityRules = attributes.getIdentityRules();
        for (Iterator<OysterRule> it = identityRules.iterator(); it.hasNext();){
            OysterRule or = it.next();
            if (temp.contains(or.getRuleIdentifer().toUpperCase(Locale.US))){
                StringBuilder sb = new StringBuilder(150);
                sb.append("##ERROR: Rule Identifier: ")
                  .append(or.getRuleIdentifer())
                  .append(" has already been used.");
                logger.severe(sb.toString());
                System.out.println(sb.toString());
                flag = false;
            } else {
                temp.add(or.getRuleIdentifer().toUpperCase(Locale.US));
            }
        }
        return flag;
    }

    /**
     * This method validates that the Item List for each indexing rule item.
     *
     * @param attributes OysterAttributes containing the list of Identity Rules 
     * to be validated
     * @return true if the Index Items have been validated, otherwise false
     */
    private boolean validateIndexingRules(OysterAttributes attributes) {
        boolean flag = true;
        for (Iterator<IndexRule> it = attributes.getIndexingRules().iterator(); it.hasNext();){
            IndexRule ir = it.next();
            for (Iterator<String> it2 = ir.getSegments().keySet().iterator(); it2.hasNext();){
                String item = it2.next();
                boolean found = false;
                for (Iterator<OysterAttribute> it3 = attributes.getAttrComp().keySet().iterator(); it3.hasNext();) {
                    OysterAttribute oa = it3.next();
                    if (oa.getName().equalsIgnoreCase(item)) {
                        found = true;
                        break;
                    }
                }
                
                if (!found){
                    StringBuilder sb = new StringBuilder(150);
                    sb.append("##ERROR: Index Rule Item: ")
                      .append(item)
                      .append(" is not used in this Oyster Attribute file.");
                    logger.severe(sb.toString());
                    System.out.println(sb.toString());
                    flag = false;
                    break;
                }
            }
            if (!flag) {
                break;
            }
        }
        return flag;
    }
    
    /**
     * This method validates that the Scan utility used in the <code>
     * TalburtZhouInvertedIndex</code> is correct. If other Scan like utilities 
     * are added they will be validated in this method also.
     * @param attributes OysterAttributes containing the list of Indexing Rules 
     * to be validated
     * @return true if the Index Rules have been validated, otherwise false
     */
    private boolean validateIndexingScanRules(OysterAttributes attributes) {
        boolean flag = true;
        StringBuilder sbRules = new StringBuilder();
        sbRules.append("Indexing Rules").append(System.getProperty("line.separator"));
        for (Iterator<IndexRule> it = attributes.getIndexingRules().iterator(); it.hasNext();){
            IndexRule ir = it.next();
            
            sbRules.append("Rule: ").append(ir.getRuleIdentifier()).append(System.getProperty("line.separator"));
            for (Iterator<String> it2 = ir.getSegments().keySet().iterator(); it2.hasNext();){
                String item = it2.next();
                String hashCode = ir.getSegments().get(item);
                
                sbRules.append("\t").append(item).append("\t").append(hashCode).append(System.getProperty("line.separator"));
                if (hashCode.toUpperCase(Locale.US).startsWith("SCAN(")) {
                    String matchType = hashCode.trim().substring(5, hashCode.length() - 1);
                    String[] args = matchType.split("[,]");
                    for (int i = 0; i < args.length; i++) {
                        switch (i) {
                            case 0:
                                if (!args[i].trim().equalsIgnoreCase("LR") && !args[i].trim().equalsIgnoreCase("RL")) {
                                    StringBuilder sb = new StringBuilder(150);
                                    sb.append("##ERROR: Invalid values for the Direction parameter. The correct values are 'LR' and 'RL'.");
                                    logger.severe(sb.toString());
                                    flag = false;
                                }
                                break;
                            case 1:
                                if (!args[i].trim().equalsIgnoreCase("ALL") && !args[i].trim().equalsIgnoreCase("NONBLANK") &&
                                    !args[i].trim().equalsIgnoreCase("ALPHA") && !args[i].trim().equalsIgnoreCase("LETTER") &&
                                    !args[i].trim().equalsIgnoreCase("DIGIT")) {
                                    StringBuilder sb = new StringBuilder(150);
                                    sb.append("##ERROR: Invalid values for the CharType parameter. The correct values are 'ALL', 'NONBLANK', 'ALPHA', 'LETTER' and 'DIGIT'.");
                                    logger.severe(sb.toString());
                                    flag = false;
                                }
                                break;
                            case 2:
                                int length = 0;
                                try {
                                    length = Integer.parseInt(args[i].trim());
                                } catch (RuntimeException ex) {
                                    StringBuilder sb = new StringBuilder(150);
                                    sb.append(ex.getMessage());
                                    logger.severe(sb.toString());
                                    flag = false;
                                }
        
                                if (length < 0 || length > 30) {
                                    StringBuilder sb = new StringBuilder(150);
                                    sb.append("##ERROR: The Length parameter must be an integer value between 0 and 30.");
                                    logger.severe(sb.toString());
                                    flag = false;
                                }
                                break;
                            case 3:
                                if (!args[i].trim().equalsIgnoreCase("ToUpper") && !args[i].trim().equalsIgnoreCase("KeepCase")) {
                                    StringBuilder sb = new StringBuilder(150);
                                    sb.append("##ERROR: Invalid values for the UpperCase parameter. The correct values are 'ToUpper' and 'KeepCase'.");
                                    logger.severe(sb.toString());
                                    flag = false;
                                }
                                break;
                            case 4:
                                if (!args[i].trim().equalsIgnoreCase("SameOrder") && !args[i].trim().equalsIgnoreCase("L2HKeepDup") &&
                                    !args[i].trim().equalsIgnoreCase("L2HDropDup")) {
                                    StringBuilder sb = new StringBuilder(150);
                                    sb.append("##ERROR: Invalid values for the Order parameter. The correct values are 'SameOrder', 'L2HKeepDup', and 'L2HDropDup'.");
                                    logger.severe(sb.toString());
                                    flag = false;
                                }
                                break;
                            default:
                                StringBuilder sb = new StringBuilder(150);
                                sb.append("##ERROR: Unknown Scan arguement: ").append(args[i]);
                                logger.severe(sb.toString());
                                flag = false;
                        }
                    }
                }
            }
            sbRules.append(System.getProperty("line.separator"));
            
            if (!flag) {
                break;
            }
        }
        
        // if passed output the rules
        if (flag){
            sbRules.append(System.getProperty("line.separator"));
            logger.severe(sbRules.toString());
        }
        return flag;
    }
        
    /**
     * This method check to ensure that the rule identifiers are unique.
     * @param attributes the list of Identity Rules to be validated
     * @return true if the rules numbering is unique, otherwise false
     */
    public boolean validateIndexingRuleNumbering(OysterAttributes attributes){
        boolean flag = true;
        Set<String> temp = new LinkedHashSet<String>();
        ArrayList<IndexRule> indexingRules = attributes.getIndexingRules();
        for (Iterator<IndexRule> it = indexingRules.iterator(); it.hasNext();){
            IndexRule ir = it.next();
            if (temp.contains(ir.getRuleIdentifier().toUpperCase(Locale.US))){
                StringBuilder sb = new StringBuilder(150);
                sb.append("##ERROR: Indexing Rule Identifier: ")
                  .append(ir.getRuleIdentifier())
                  .append(" has already been used.");
                logger.severe(sb.toString());
                System.out.println(sb.toString());
                flag = false;
            } else {
                temp.add(ir.getRuleIdentifier().toUpperCase(Locale.US));
            }
        }
        return flag;
    }
        
        public boolean validateSourceDescriptorNames(Set<String> sources) {
        boolean flag = true;

        if (sources != null) {
            for (Iterator<String> it = sources.iterator(); it.hasNext();) {
                String file = it.next();
                // read sourceDescriptor script (XML)
                SourceDescriptorParser sdParser = new SourceDescriptorParser();
                OysterReferenceSource s = sdParser.parse(file);

                if (sourceNames.contains(s.getSourceName())) {
                    flag = false;
                    break;
                }

                sourceNames.add(s.getSourceName());
            }
        }
        return flag;
    }

    private void preloadIndex() throws Exception{
        // loop thru each source and load the index
        for (Iterator<String> it = getRunScript().getSources().iterator(); it.hasNext();) {
            String file = it.next();

            // read sourceDescriptor script (XML)
            SourceDescriptorParser sdParser = new SourceDescriptorParser();
            OysterReferenceSource ors = sdParser.parse(file);

            // open the reference source
            if (ors.getSourceType().equalsIgnoreCase("FileDelim")) {
                OysterDelimitedReader osr = new OysterDelimitedReader(ors.getSourcePath(), ors.getDelimiter(), ors.getQualifer(), ors.isLabel(), ors.getReferenceItems(), logger);
                osr.open();
                ors.setSourceReader(osr);
            } else if (ors.getSourceType().equalsIgnoreCase("FileFixed")) {
                OysterFixedWidthReader osr = new OysterFixedWidthReader(ors.getSourcePath(), ors.getReferenceItems(), logger);
                osr.open();
                ors.setSourceReader(osr);
            } else if (ors.getSourceType().equalsIgnoreCase("Database")) {
                OysterDatabaseReader osr = new OysterDatabaseReader(ors.getSourcePath(), ors.getConnectionType(), ors.getServer(), ors.getPort(), ors.getSid(), ors.getUserID(), ors.getPasswd(), ors.getReferenceItems(), logger);
                if (osr.isConnected()) {
                    osr.open();
                }
                ors.setSourceReader(osr);
            }

            ors.getSourceReader().setSource(ors.getSourceName());
            
            // load the index
            while (ors.getSourceReader().getNextReference() > 0) {
                ClusterRecord cr = ors.getSourceReader().getClusterRecord();
                for (int i = 0; i < cr.getSize(); i++) {
                    getRepository().addIndex(cr.getOysterIdentityRecord(i));
                }
            }
        }
    }

    private void syncOysterIdentityRecord() {
        OysterIdentityRecord tempOIR;
        
        switch (recordType) {
            case RecordTypes.CODOSA: tempOIR = new CoDoSAOIR(); break;
            case RecordTypes.MAP: tempOIR = new OysterIdentityRecordMap(); break;
            default: tempOIR = new OysterIdentityRecordMap();
        }
        
        tempOIR.updateMetaData();
    }
    
    //==========================================================================
    //  ... Garbage Collection Methods
    //==========================================================================
    /** this is our way of requesting garbage collection to be run:
     * [how aggressive it is depends on the JVM to a large degree, but
     * it is almost always better than a single Runtime.gc() call]
     */
    private static void runGC() throws Exception {
        // for whatever reason it helps to call Runtime.gc()                 
        // using several method calls:                 
        for (int r = 0; r < 4; ++r) {
            _runGC();
        }
    }

    @SuppressWarnings("static-access")
    private static void _runGC() throws Exception {
        long usedMem1 = usedMemory(), usedMem2 = Long.MAX_VALUE;
        for (int i = 0; (usedMem1 < usedMem2) && (i < 1000); ++i) {
            s_runtime.runFinalization();
            s_runtime.gc();
            Thread.currentThread().yield();
            usedMem2 = usedMem1;
            usedMem1 = usedMemory();
        }
    }

    private static long usedMemory() {
        return s_runtime.totalMemory() - s_runtime.freeMemory();
    }
    
    //==========================================================================
    //  ... Stats Methods
    //==========================================================================
    /**
     * The method calculates the runtime statistics for this ER run.
     */
    public void outputStats(long elaspedSecs) {
        long count = 0, sum = 0, sumGroup = 0, sumCount = 0, dups = 0;
        StringBuilder sb = new StringBuilder();
        
        // Send all output to the Appendable object sb
        Formatter report = new Formatter(sb, Locale.US);
        
        clusterFreq = getRepository().getClusterDistribution();
        if (!clusterFreq.isEmpty()){
            maxGroupSize = clusterFreq.lastKey();
        
            if (clusterFreq.size() > 1) {
                minGroupSizeGT1 = clusterFreq.ceilingKey(2L);
            }
            minGroupSize = clusterFreq.firstKey();
        }

        sb.append(System.getProperty("line.separator"));
        sb.append("###################").append(System.getProperty("line.separator"));
        sb.append("## Summary Stats ##").append(System.getProperty("line.separator"));
        sb.append("###################").append(System.getProperty("line.separator"));
        report.format("Total Records Processed          : %1$,12d%n", totalRecords);
        report.format("Total Clusters                   : %1$,12d%n", groups);
        report.format("Max Cluster Size                 : %1$,12d%n", maxGroupSize);
        report.format("Min Cluster Size > 1             : %1$,12d%n", minGroupSizeGT1);
        report.format("Min Cluster Size                 : %1$,12d%n", minGroupSize);
        sb.append(System.getProperty("line.separator"));
        sb.append(System.getProperty("line.separator"));
        
        sb.append("###################").append(System.getProperty("line.separator"));
        sb.append("## Cluster Stats ##").append(System.getProperty("line.separator"));
        sb.append("###################").append(System.getProperty("line.separator"));
        sb.append("Cluster Size Distribution").append(System.getProperty("line.separator"));
        sb.append("Cluster Size     # of Clusters        # of Records").append(System.getProperty("line.separator"));
        
        for (Iterator<Long> it = clusterFreq.keySet().iterator(); it.hasNext();) {
            long key = it.next();
            long value = clusterFreq.get(key);
            
            report.format("%1$,12d     %2$,13d     %3$,15d%n", key, value, key*value);
            
            sumGroup += key;
            sumCount += value;
            sum += key*value;
            
            if (key > 1L) {
                dups += (key-1)*value;
            }
            
            count++;
        }
        sb.append(System.getProperty("line.separator"));
        if (count != 0){
            avgClusterGroup = sumGroup / count;
            avgClusterCount = sumCount / count;
        }
        avgClusterSize = (double)sum / (double)sumCount;
//        duplicationRate = (double)dups / (double)sum;
        duplicationRate = 1d - ((double)groups / (double)totalRecords);

        report.format("Clusters loaded                  : %1$,12d%n", getRepository().getNumOfClusters());
        report.format("References loaded                : %1$,12d%n", getRepository().getNumOfReferences());
        report.format("Avg # of Refs/Cluster            : %1$,12.5f%n", (float)getRepository().getNumOfReferences()/(float)getRepository().getNumOfClusters());
        sb.append(System.getProperty("line.separator"));
        sb.append(System.getProperty("line.separator"));
        
        report.format("Average Cluster Grouping         : %1$,12d%n", avgClusterGroup);
        report.format("Average Cluster by Count         : %1$,12d%n", avgClusterCount);
        report.format("Average Cluster Size             : %1$,12.5f%n", avgClusterSize);
        report.format("Number of Duplicate Recs         : %1$,12d%n", dups);
        report.format("Duplication Rate                 : %1$,12.5f%n", duplicationRate);
        sb.append(System.getProperty("line.separator"));
        sb.append(System.getProperty("line.separator"));
        
        report.format("Total Candidates Size            : %1$,12d%n", getEngine().getTotalCandidatesSize());
        report.format("Total DeDup Candidates Size      : %1$,12d%n", getEngine().getTotalCandidatesDeDupSize());
        report.format("Total # Candidates               : %1$,12d%n", getEngine().getTotalCandidates());
        report.format("Avg Candidates per Input         : %1$,12.5f%n", (float)getEngine().getTotalCandidatesSize() / (float)getEngine().getTotalCandidates());
        report.format("Total Matched Count              : %1$,12d%n", getEngine().getTotalMatchedCount());
        report.format("Matches per Candidates Size      : %1$,12.5f%n", (float)getEngine().getTotalMatchedCount() / (float)getEngine().getTotalCandidatesSize());
        report.format("Matches per DeDup Candidates Size: %1$,12.5f%n", (float)getEngine().getTotalMatchedCount() / (float)getEngine().getTotalCandidatesDeDupSize());
        report.format("Matches per Candidates           : %1$,12.5f%n", (float)getEngine().getTotalMatchedCount() / (float)getEngine().getTotalCandidates());
        
        sb.append(System.getProperty("line.separator"));
        sb.append(System.getProperty("line.separator"));
        
        sb.append("#########################").append(System.getProperty("line.separator"));
        sb.append("##   First Rule Stats  ##").append(System.getProperty("line.separator"));
        sb.append("#########################").append(System.getProperty("line.separator"));
        sb.append("Number of Rules: ").append(numRules).append(System.getProperty("line.separator"));
        sb.append("Rule Firing Distribution").append(System.getProperty("line.separator"));
        sb.append("Rule                          Counts").append(System.getProperty("line.separator"));
        for (Iterator<String> it = ruleFreq.keySet().iterator(); it.hasNext();) {
            String key = it.next();
            long value = ruleFreq.get(key);
            
            report.format("%1$-15s     %2$,15d%n", key, value);
        }
        sb.append(System.getProperty("line.separator"));
        sb.append(System.getProperty("line.separator"));
        
        sb.append("############################").append(System.getProperty("line.separator"));
        sb.append("##   Complete Rule Stats  ##").append(System.getProperty("line.separator"));
        sb.append("############################").append(System.getProperty("line.separator"));
        sb.append("Rule Firing Distribution").append(System.getProperty("line.separator"));
        sb.append("Rule                          Counts").append(System.getProperty("line.separator"));
        for (Iterator<String> it = completeRuleFiring.keySet().iterator(); it.hasNext();) {
            String key = it.next();
            long value = completeRuleFiring.get(key);
        
            report.format("%1$-15s     %2$,15d%n", key, value);
        }
        sb.append(System.getProperty("line.separator"));
        sb.append(System.getProperty("line.separator"));

        sb.append("###################").append(System.getProperty("line.separator"));
        sb.append("##  Index Stats  ##").append(System.getProperty("line.separator"));
        sb.append("###################").append(System.getProperty("line.separator"));
        if (runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_MERGE_PURGE) ||
            runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_RECORD_LINKAGE) ||
            runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_CAPTURE) ||
            runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_UPDATE) ||
            runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_RESOLVE)) {
            sb.append(index.indexStats());
            sb.append(System.getProperty("line.separator"));
            sb.append(System.getProperty("line.separator"));
        }
        sb.append(System.getProperty("line.separator"));
        sb.append(System.getProperty("line.separator"));
        
        if (runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_RESOLVE)) {
            sb.append("########################").append(System.getProperty("line.separator"));
            sb.append("##  Resolution Stats  ##").append(System.getProperty("line.separator"));
            sb.append("########################").append(System.getProperty("line.separator"));
            report.format("Records resolved                 : %1$,12d%n", getEngine().getResolvedRecords());
            sb.append(System.getProperty("line.separator"));
            sb.append(System.getProperty("line.separator"));
        }
        sb.append(System.getProperty("line.separator"));
        sb.append(System.getProperty("line.separator"));
        
        sb.append("####################").append(System.getProperty("line.separator"));
        sb.append("##  Timing Stats  ##").append(System.getProperty("line.separator"));
        sb.append("####################").append(System.getProperty("line.separator"));
        report.format("Elapsed Seconds                  : %1$,16d%n", elaspedSecs);
        report.format("Throughput (records/hour)        : %1$,16.5f%n", (double) totalRecords / ((double)elaspedSecs/3600d));
        report.format("Average Matching Latency (ms)    : %1$,16f%n", (float)getEngine().getMatchingLatency() / (float)totalRecords);
        report.format("Max Matching Latency (ms)        : %1$,16d%n", getEngine().getMaxMatchingLatency());
        report.format("Min Matching Latency (ms)        : %1$,16d%n", getEngine().getMinMatchingLatency());
        report.format("Average Non-Matching Latency (ms): %1$,16.5f%n", (float)getEngine().getNonMatchingLatency() / (float)totalRecords);
        report.format("Max Non-Matching Latency (ms)    : %1$,16d%n", getEngine().getMaxNonMatchingLatency());
        report.format("Min Non-Matching Latency (ms)    : %1$,16d%n", getEngine().getMinNonMatchingLatency());
        sb.append(System.getProperty("line.separator"));
        sb.append(System.getProperty("line.separator"));
                
        logger.severe(sb.toString());
        System.out.println(sb.toString());
    }

    /**
     * The method calculates the current memory usage of the entire ER system.
     */
    public void systemStats(){
        long heapSize, heapMaxSize, heapFreeSize, heapUsedSize;
        StringBuilder sb = new StringBuilder();
        
        try{
            // clear any garbage before getting stats
            runGC();

            // Send all output to the Appendable object sb
            Formatter report = new Formatter(sb, Locale.US);
            // Get current size of heap in bytes
            heapSize = s_runtime.totalMemory();

            // Get maximum size of heap in bytes. The heap cannot grow beyond this size.
            // Any attempt will result in an OutOfMemoryException.
            heapMaxSize = s_runtime.maxMemory();

            // Get amount of free memory within the heap in bytes. This size will increase
            // after garbage collection and decrease as new objects are created.
            heapFreeSize = s_runtime.freeMemory();

            if (heapSize > heapFreeSize) {
                heapUsedSize = heapSize - heapFreeSize;
            } else {
                heapUsedSize = heapSize;
            }
            report.format("Max Heap Size : %1$,12.3fKB%n", (double) heapMaxSize / 1024D);
            report.format("Heap Size     : %1$,12.3fKB%n", (double) heapSize / 1024D);
            report.format("Used Heap Size: %1$,12.3fKB%n", (double) heapUsedSize / 1024D);
            report.format("Free Heap Size: %1$,12.3fKB%n", (double) heapFreeSize / 1024D);
            sb.append(System.getProperty("line.separator"));

            logger.severe(sb.toString());
            System.out.println(sb.toString());
        } catch (Exception ex) {
            Logger.getLogger(OysterMain.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }
    
    /**
     * This method formats the log filename
     * @param logFile
     * @return
     */
    private String formatLogFile(String logFile){
        int begin;
        // Oyster_%g.log
        if ((logFile.indexOf("%g")) == -1){
            if ((begin = logFile.lastIndexOf(".")) != -1){
                logFile = logFile.substring(0, begin) + "_%g" + logFile.substring(begin);
            } else {
                logFile = logFile + "_%g.log";
            }
        }
        return logFile;
    }
    
    //==========================================================================
    //  ... Main Methods
    //==========================================================================
    /**
     * This is the main execution point.
     * @param args
     */
    public int process(String[] args) {
        boolean sorted = false, stats = false, keepPreviousDBTable = false, error = false;
        int sortValue = 1, gc = -1, topStart = -1, topStop = -1, errorCode = 0;
        String logFile = "", rsFile = "", debugFile = "";
        Level logLevel = Level.OFF;
        Map<String, Long> totals = new LinkedHashMap<String, Long>();
        Map<String, Long> rswooshs = new LinkedHashMap<String, Long>();
        char arg;

        try {
            for (int i = 0; i < args.length; i++) {
                arg = args[i].charAt(1);
                switch (arg) {
                    case 'b':
                        topStart = Integer.parseInt(args[++i]);
                        break;
                    case 'd':
                        debugFile = args[++i];
                        break;
                    case 'e':
                        topStop = Integer.parseInt(args[++i]);
                        break;
                    case 'g':
                        gc = Integer.parseInt(args[++i]);
                        break;
                    case 'l':
                        logFile = args[++i];
                        break;
                    case 'r':
                        rsFile = args[++i];
                        break;
                    case 's':
                        sortValue = Integer.parseInt(args[++i]);
                        break;
                    case 'z':
                        stats = args[++i].equals("1") ? true : false;
                        break;
                    default:
                        System.out.println("Mode: " + arg);
                        //                          Usage();
                        return (-1);
                }
            }

            switch (sortValue) {
                case 0:
                    sorted = false;
                    break;
                case 1:
                    sorted = true;
                    break;
                default:
                    sorted = false;
            }

            // read run script (XML)
            RunScriptParser rsParser = new RunScriptParser();
            setRunScript(rsParser.parse(rsFile));

            // initialize logger
            logger = Logger.getLogger(getClass().getName());

            // remove root handlers and disable any references to root handlers
            logger.setUseParentHandlers(false);
            Logger globalLogger = Logger.getLogger("global");
            Handler[] handlers = globalLogger.getHandlers();
            for (Handler handler : handlers) {
                globalLogger.removeHandler(handler);
            }

            // add handlers
            if (runScript.getLogFile() != null) {
                logFile = runScript.getLogFile();
            }
            if (runScript.getLogFileNum() > 1) {
                logFile = formatLogFile(logFile);
            }
            fileHandler = new FileHandler(logFile, runScript.getLogFileSize(), runScript.getLogFileNum());
            fileHandler.setEncoding("UTF8");
            logger.addHandler(fileHandler);
//            consoleHandler = new ConsoleHandler();
//            logger.addHandler(consoleHandler);

            if (runScript.isDebug() && runScript.isExplanation()) {
                logLevel = Level.FINEST;
            } else if (runScript.isDebug() && !runScript.isExplanation()) {
                logLevel = Level.FINE;
            } else if (!runScript.isDebug() && runScript.isExplanation()) {
                logLevel = Level.INFO;
            } else if (!runScript.isDebug() && !runScript.isExplanation()) {
                logLevel = Level.SEVERE;
            }

            // set Garbage Collection
            gc = runScript.getGc();

            // set level and formatter
            logger.setLevel(logLevel);
            OysterExplanationFormatter formatter = new OysterExplanationFormatter();
            fileHandler.setFormatter(formatter);

            StringBuilder sb = new StringBuilder(150);
            sb.append("Oyster v.")
              .append(this.getVersion())
              .append(System.getProperty("line.separator"));
            sb.append("RunScript: ")
              .append(rsFile)
              .append(System.getProperty("line.separator"));
            sb.append("Attribute: ")
              .append(runScript.getAttributeLocation());
            logger.severe(sb.toString());

            startTime = now();

            // if there are debug records read them in
            if (!debugFile.equals("")) {
                loadDebug(debugFile);
            }
            
            // validate RunScript
            if (validateRunScript(rsFile)) {
                // create a single instance of OysterAttributes
                AttributesParser aParser = new AttributesParser();
                setAttributes(aParser.parse(runScript.getAttributeLocation()));

                // check to see if the system stats flag was set in the run script
                if (!stats) {
                    stats = runScript.isSystemStats();
                }

                // get the system stats before starting
                if (stats) {
                    System.out.println("System stats before starting");
                    logger.severe("System stats before starting");
                    systemStats();
                }

                // Validate Item Names in Identity Rules against Item Names in Reference Items
                if (validateAttributes(attributes)) {
                    // Instantiate Comparators
                    initializeComparators();

                    // validate rule matchCodes against Compatators
                    if (validateRuleMatchCodes(attributes) && 
                        validateRuleNumbering(attributes) && 
                        validateIndexingRules(attributes) &&
                        validateIndexingScanRules(attributes) &&
                        validateIndexingRuleNumbering(attributes)) {

                        //==========================================================================
                        // Initializing the Index
                        //==========================================================================
                        logger.severe("Initializing Index...");
                        System.out.println(System.getProperty("line.separator") + "Initializing Index...");

//                        if (runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_MERGE_PURGE) ||
//                                runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_CAPTURE) ||
//                                runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_RESOLVE) ||
//                                runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_UPDATE)) {
                            if (attributes.getIndexingRules() != null && !attributes.getIndexingRules().isEmpty()){
                                TalburtZhouInvertedIndex tzIndex = new TalburtZhouInvertedIndex();
                                tzIndex.setRules(attributes.getIndexingRules());
                                index = tzIndex;
                            } else {
                                index = new NullIndex();
                            }
                        
                        sb = new StringBuilder(100);
                        sb.append("Index Type: ")
                          .append(index.getClass().getSimpleName())
                          .append(System.getProperty("line.separator"));
                        System.out.println(sb.toString());
                        logger.severe(sb.toString());
                        
                        index.setPassThruAttributes(passThruAttributes);

                        //==========================================================================                    
                        // Initialize the Record & Cluster Types
                        // These are hardcoded right now but should become dynamic in the future
                        //==========================================================================
                        // OysterIdentityRecord Type
                        String type;
                        recordType = RecordTypes.MAP;
                        switch (recordType){
                            case RecordTypes.CODOSA: type = "CoDoSA"; break;
                            case RecordTypes.MAP: type = "Map"; break;
                            default: type = "Map";
                        }
                        sb = new StringBuilder(100);
                        sb.append("OysterIdentityRecord Type: ")
                          .append(type)
                          .append(System.getProperty("line.separator"));
                        System.out.println(sb.toString());
                        logger.severe(sb.toString());

                        // ClusterRecord Type
                        switch (clusterType){
                            case ClusterTypes.MAP: type = "Map"; break;
                            default: type = "UNKNOWN";
                        }
                        clusterType = ClusterTypes.MAP;
                        sb = new StringBuilder(100);
                        sb.append("ClusterRecord Type: " )
                          .append(type)
                          .append(System.getProperty("line.separator"));
                        System.out.println(sb.toString());
                        logger.severe(sb.toString());
                        
                        
                        //==========================================================================                    
                        // Initialize the EntityMap
                        //==========================================================================
                        logger.severe("Initializing EntityMap...");
                        System.out.println(System.getProperty("line.separator") + "Initializing EntityMap...");

                        if (runScript.getEntityMapType() == null) {
                            entityMap = new EntityMap(new LinkedHashMap<String, ClusterRecord>(), recordType);
                        } else if (runScript.getEntityMapType().equalsIgnoreCase("EntityMap")) {
                            entityMap = new EntityMap(new LinkedHashMap<String, ClusterRecord>(), recordType);
                        } else if (runScript.getEntityMapType().equalsIgnoreCase("DBEntityMap")) {
                            DBEntityMap dbEntityMap = new DBEntityMap(new LinkedHashMap<String, ClusterRecord>(), runScript.getEntityMapCType(), runScript.getEntityMapServer(), runScript.getEntityMapPort(), runScript.getEntityMapSID(), runScript.getEntityMapUserID(), runScript.getEntityMapPasswd(), recordType);
                            if (dbEntityMap.isConnected(keepPreviousDBTable)) {
                                entityMap = dbEntityMap;
                            } else {
                                return (-1000);
                            }
                        } else {
                            try {
                                Class comp = Class.forName(runScript.getEntityMapType());
                                entityMap = (EntityMap) comp.newInstance();
                            } catch (Exception ex) {
                                sb = new StringBuilder(100);
                                sb.append("Unknown or Invalid EntityMap Class: ")
                                  .append(runScript.getEntityMapType())
                                  .append(System.getProperty("line.separator"));
                                sb.append("Initializing EntityMap by Default.");
                                logger.severe(sb.toString());
                                entityMap = new EntityMap(new LinkedHashMap<String, ClusterRecord>(), recordType);
                            }
                        }
                        sb = new StringBuilder(100);
                        sb.append("EntityMap Type: ")
                          .append(entityMap.getClass().getSimpleName())
                          .append(System.getProperty("line.separator"));
                        logger.severe(sb.toString());
                        System.out.println(sb.toString());

                        // open the outputs for this mode
                        if (openOysterOutputs(keepPreviousDBTable)) {
                            if (this.validateSourceDescriptorNames(runScript.getSources())) {
                                //==================================================================
                                // Create the ER engine
                                //==================================================================
                                if (runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_MERGE_PURGE) ||
                                    runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_RECORD_LINKAGE) ||
                                    runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_CAPTURE) ||
                                    runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_RESOLVE) ||
                                    runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_UPDATE)) {
                                    if (runScript.getEngineType() != null && runScript.getEngineType().equalsIgnoreCase("RSwooshStandard")) {
                                        setEngine(new OysterMergeEngine(logger, recordType));
                                    } else if (runScript.getEngineType() != null && runScript.getEngineType().equalsIgnoreCase("RSwooshEnhanced")) {
                                        setEngine(new OysterMergeConsolidationEngine(logger, recordType));
                                    } else if (runScript.getEngineType() != null && runScript.getEngineType().equalsIgnoreCase("FSCluster")) {
                                        setEngine(new OysterClusterEngine(logger, recordType));
                                    } else {
                                        setEngine(new OysterMergeEngine(logger, recordType));
                                    }

                                    // set the rule list for the engine
                                    ((OysterResolutionEngine) engine).setRuleList(attributes.getIdentityRules());
                                    ((OysterResolutionEngine) engine).setAttributes(attributes);
                                    ((OysterResolutionEngine) engine).setRuleFreq(ruleFreq);
                                    ((OysterResolutionEngine) engine).setCompleteRuleFiring(completeRuleFiring);
                                } else {
                                    setEngine(new OysterAssertionEngine(logger, "@"+runScript.getRunMode(), recordType));
                                }

                                sb = new StringBuilder(100);
                                sb.append("Engine Type: ")
                                  .append(engine.getClass().getSimpleName())
                                  .append(System.getProperty("line.separator"));
                                logger.severe(sb.toString());
                                System.out.println(sb.toString());

                                // set Repository Metadata
                                repository.setDate(now());
                                repository.setRunScriptName(runScript.getName());
                                repository.setOysterVersion(version);

                                // set the ER engine parameters
                                engine.setRepository(repository);
                                engine.setDebug(runScript.isDebug());

                                // do I need to preload the index?
                                if (runScript.isPreLoad()) {
                                    logger.severe("Preloading the Index...");
                                    System.out.println(System.getProperty("line.separator") + "Preloading the Index...");
                                    preloadIndex();
                                }

                                if (runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_MERGE_PURGE) ||
                                    runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_RECORD_LINKAGE) ||
                                    runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_CAPTURE) ||
                                    runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_RESOLVE) ||
                                    runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_UPDATE)) {
                                    ((OysterResolutionEngine) engine).setByPassFilter(runScript.isBypassFilter());

                                    // deterimine the least common rule denominator
                                    if (!((OysterResolutionEngine) engine).isByPassFilter()) {
                                        if (runScript.getLcrd() != null && runScript.getLcrd().size() > 0) {
                                            ((OysterResolutionEngine) engine).setPrimaryFilter(runScript.getLcrd());
                                            ((OysterResolutionEngine) engine).setSecondaryFilter(lcrd(attributes.getIdentityRules()));
                                        } else {
                                            ((OysterResolutionEngine) engine).setPrimaryFilter(lcrd(attributes.getIdentityRules()));
                                        }
                                        sb = new StringBuilder(100);
                                        sb.append("Primary Least Common Rules for the source are: ")
                                          .append(((OysterResolutionEngine) engine).getPrimaryFilter())
                                          .append(System.getProperty("line.separator"));
                                        sb.append("Secondary Least Common Rules for the source are: ")
                                          .append(((OysterResolutionEngine) engine).getSecondaryFilter())
                                          .append(System.getProperty("line.separator"));
                                        logger.severe(sb.toString());
                                        System.out.println(sb.toString());
                                    } else {
                                        System.out.println(System.getProperty("line.separator") + "Bypassing Least Common Rule filter");
                                        logger.severe("Bypassing Least Common Rule filter");
                                    }
                                    System.out.println();
                                    logger.severe(System.getProperty("line.separator"));

                                    for (Iterator<String> it = runScript.getSources().iterator(); it.hasNext();) {
                                        String file = it.next();

                                        if (runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_MERGE_PURGE) ||
                                            runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_RECORD_LINKAGE) ||
                                            runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_CAPTURE) ||
                                            runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_IDENT_UPDATE)) {
                                            engine.setCapture(true);
                                        } else {
                                            engine.setCapture(false);
                                        }

                                        // read sourceDescriptor script (XML)
                                        SourceDescriptorParser sdParser = new SourceDescriptorParser();
                                        source = sdParser.parse(file);

                                        sb = new StringBuilder(100);
                                        sb.append("Source: ")
                                          .append(source.getSourcePath())
                                          .append(System.getProperty("line.separator"));
                                        logger.severe(sb.toString());
                                        System.out.println(sb.toString());

                                        // Validate the attribute names in the metadata for Reference Items
                                        if (validateReferences(source, attributes)) {
                                            // sync the oir metadata
                                            syncOysterIdentityRecord();
                                        
                                            // open the reference source
                                            if (source.getSourceType().equalsIgnoreCase("FileDelim")) {
                                                OysterDelimitedReader osr = new OysterDelimitedReader(source.getSourcePath(), source.getDelimiter(), source.getQualifer(), source.isLabel(), source.getReferenceItems(), logger);
                                                osr.open();
//                                    osr.setCountPoint(1000);
                                                source.setSourceReader(osr);
                                            } else if (source.getSourceType().equalsIgnoreCase("FileFixed")) {
                                                OysterFixedWidthReader osr = new OysterFixedWidthReader(source.getSourcePath(), source.getReferenceItems(), logger);
                                                osr.open();
                                                source.setSourceReader(osr);
                                            } else if (source.getSourceType().equalsIgnoreCase("Database")) {
                                                OysterDatabaseReader osr = new OysterDatabaseReader(source.getSourcePath(), source.getConnectionType(), source.getServer(), source.getPort(), source.getSid(), source.getUserID(), source.getPasswd(), source.getReferenceItems(), logger);
                                                osr.setOverRideSQL(source.getOverRideSQL());
                                            
                                                if (osr.isConnected()) {
                                                    osr.open();
                                                }
                                                source.setSourceReader(osr);
                                            }
//======================================
// CAN I MOVE THIS OUTSIDE THE LOOP
//======================================
                                            engine.setCurrentSourceName(source.getSourceName());
                                            source.getSourceReader().setSource(source.getSourceName());

                                            // set engine options for this sources run
                                            source.getSourceReader().getClusterRecord().setCurrentRunID(repository.getMid());
                                            engine.setClusterRecord(source.getSourceReader().getClusterRecord());

                                            // Create Optimized Rule Matrix
                                            ((OysterResolutionEngine) engine).createMatrix();
                                            ((OysterResolutionEngine) engine).populateMasks();
//======================================
//======================================
                                            // get the system stats before reading current source
                                            if (stats) {
                                                System.out.println("System stats before reading current source");
                                                logger.severe("System stats before reading current source");
                                                systemStats();
                                            }

                                            String start, stop;
                                            start = now();
                                            while (source.getSourceReader().getNextReference() > 0 && !die) {
                                                if (debugRecords.contains(source.getSourceReader().getClusterRecord().getMergedRecord().get("@RefID"))){
                                                    logger.setLevel(Level.FINEST);
                                                }
//                                    isNotJunk()
                                                {
/*
                                                if (repository.isDebug()) {
                                                    System.out.println("## Record Count    : " + source.getSourceReader().getRecordCount());
                                                }
*/
                                                    // Ask ResolutionEngine to resolve reference
                                                    ((OysterResolutionEngine) engine).integrateSource(sorted, source.getSourceReader().getRecordCount());

                                                    // How long does it take to pull the clusters per 10,000
                                                    if (entityMap.getClass().getSimpleName().equalsIgnoreCase("DBEntityMap")) {
                                                        if (source.getSourceReader().getRecordCount() % 10000 == 0) {
                                                            stop = now();
                                                            long elasped = elapsedSecs(start, stop);
                                                            String s = "Total elapsed time " + source.getSourceReader().getRecordCount() +
                                                                    "\t" + elasped +
                                                                    "\t" + ((DBEntityMap) entityMap).getDatabaseCallInfo();
                                                            logger.severe(s);
                                                            System.out.println(s);
                                                            start = now();
                                                            ((DBEntityMap) entityMap).clearDatabaseCallInfo();
                                                        }
                                                    }

                                                    // Check for Garbage Collection
                                                    if (gc > -1 && source.getSourceReader().getRecordCount() % gc == 0) {
                                                        System.out.println("Collecting Garbage");
                                                    
                                                        if (entityMap.getClass().getSimpleName().equalsIgnoreCase("DBEntityMap")) {
                                                            repository.getEntityMap().clear();
                                                        }
                                                    
                                                        runGC();
                                                    }

                                                    // turn on/off debug flag
                                                    if (source.getSourceReader().getRecordCount() == topStart) {
                                                        repository.setDebug(true);
                                                    } else if (source.getSourceReader().getRecordCount() == topStop) {
                                                        repository.setDebug(false);
                                                    }
                                                }
                                            
                                                // turn off
                                                if (debugRecords.contains(source.getSourceReader().getClusterRecord().getMergedRecord().get("@RefID"))){
                                                    logger.setLevel(logLevel);
                                                }
                                            }

                                            if (((OysterResolutionEngine) engine).hasPostConsolidation()) {
                                                // get the system stats Pre RSwoosh
                                                if (stats) {
                                                    System.out.println("System stats Pre RSwoosh");
                                                    logger.severe("System stats Pre RSwoosh");
                                                    systemStats();
                                                }

                                                ((OysterResolutionEngine) engine).postConsolidation(sorted, source.getSourceReader().getRecordCount(), source.getSourceReader().getCountPoint());
                                            }

                                            // get the system stats post RSwoosh
                                            if (stats) {
                                                if (((OysterResolutionEngine) engine).hasPostConsolidation()) {
                                                    System.out.println("System stats Post RSwoosh");
                                                    logger.severe("System stats Post RSwoosh");
                                                } else {
                                                    System.out.println("System stats After Run");
                                                    logger.severe("System stats After Run");
                                                }
                                                systemStats();
                                            }

                                            // close the source
                                            source.getSourceReader().close();

                                            totals.put(file, source.getSourceReader().getRecordCount() - 1);
                                            rswooshs.put(file, ((OysterResolutionEngine) engine).getTempCounter());
                                            totalRecords += source.getSourceReader().getRecordCount() - 1;
                                            totalRSwooshs += ((OysterResolutionEngine) engine).getTempCounter();
                                            ((OysterResolutionEngine) engine).setTempCounter(0);
                                        } else {
                                            System.out.println("##ERROR: Reference Items and Attributes do not match.");
                                            logger.severe("##ERROR: Reference Items and Attributes do not match.");
                                            error = true;
                                        }
                                    }
                                    System.out.println();
                                    for (Iterator<Entry<String, Long>> it = totals.entrySet().iterator(); it.hasNext();) {
                                        Entry<String, Long> entry = it.next();
                                        long count = entry.getValue();
                                        long rswoosh = rswooshs.get(entry.getKey());
                                        sb = new StringBuilder(100);
                                        sb.append("Records processed for ")
                                          .append(entry.getKey())
                                          .append(": ")
                                          .append(count)
                                          .append("(")
                                          .append(rswoosh)
                                          .append(")")
                                          .append(System.getProperty("line.separator"));
                                        logger.severe(sb.toString());
                                        System.out.println(sb.toString());
                                    }
                                    sb = new StringBuilder(100);
                                    sb.append("# of Consolidation Steps: ")
                                      .append(totalRSwooshs)
                                      .append(System.getProperty("line.separator"));
                                    logger.severe(sb.toString());
                                    System.out.println(sb.toString());
                                } else {
                                    // read sourceDescriptor script (XML)
                                    SourceDescriptorParser sdParser = new SourceDescriptorParser();
                                    source = sdParser.parse(runScript.getAssertionInputLocation());

                                    // Validate the attribute names in the metadata for Reference Items
                                    if (validateReferences(source, attributes)) {
                                        // sync the oir metadata
                                        syncOysterIdentityRecord();
                                    
                                        sb = new StringBuilder(100);
                                        sb.append("Source: ")
                                          .append(source.getSourcePath())
                                          .append(System.getProperty("line.separator"));
                                        logger.severe(sb.toString());
                                        System.out.println(sb.toString());

                                        OysterDelimitedReader osr = new OysterDelimitedReader(source.getSourcePath(), source.getDelimiter(), source.getQualifer(), source.isLabel(), source.getReferenceItems(), logger);
                                        osr.open();
//                                        osr.setCountPoint(1000);
                                        source.setSourceReader(osr);
//======================================
// CAN I MOVE THIS OUTSIDE THE LOOP
//======================================
                                        engine.setCurrentSourceName(source.getSourceName());
                                        source.getSourceReader().setSource(source.getSourceName());

                                        // set engine options for this sources run
                                        source.getSourceReader().getClusterRecord().setCurrentRunID(repository.getMid());
                                        engine.setClusterRecord(source.getSourceReader().getClusterRecord());
//======================================
//======================================
                                        // get the system stats before reading current source
                                        if (stats) {
                                            System.out.println("System stats before reading current source");
                                            logger.severe("System stats before reading current source");
                                            systemStats();
                                        }
                                    
                                        while (source.getSourceReader().getNextReference() > 0 && !((OysterAssertionEngine) engine).isBadAssert() && !die) {
                                            if (runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_REF2REF)) {
                                                ((OysterAssertionEngine) engine).assertRefToRef(source.getSourceReader().getRecordCount());
                                            } else if (runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_REF2STR)) {
                                                ((OysterAssertionEngine) engine).assertRefToStr(source.getSourceReader().getRecordCount());
                                            } else if (runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_STR2STR)) {
                                                ((OysterAssertionEngine) engine).assertStrToStr(source.getSourceReader().getRecordCount());
                                            } else if (runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_SPLIT_STR)) {
                                                ((OysterAssertionEngine) engine).assertSplitStr(source.getSourceReader().getRecordCount());
                                            }
                                        }
                                    
                                        if (((OysterAssertionEngine) engine).isBadAssert()) {
                                            error = true;
                                            errorCode = ((OysterAssertionEngine) engine).getAssertCode();
                                        } else {
                                            // handle the last record group
                                            if (runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_STR2STR)) {
                                                ((OysterAssertionEngine) engine).postAssertStrToStr(source.getSourceReader().getRecordCount());
                                            } else if (runScript.getRunMode().equalsIgnoreCase(OysterKeywords.RUNMODE_ASSERT_SPLIT_STR)) {
                                                ((OysterAssertionEngine) engine).postAssertNegStr(source.getSourceReader().getRecordCount());
                                                ((OysterAssertionEngine) engine).postNeg();
                                    
                                                if (((OysterAssertionEngine) engine).isBadAssert()) {
                                                    error = true;
                                                    errorCode = ((OysterAssertionEngine) engine).getAssertCode();
                                                }
                                            }
                                        }
                                    } else {
                                        System.out.println("##ERROR: Reference Items and Attributes do not match.");
                                        logger.severe("##ERROR: Reference Items and Attributes do not match.");
                                        error = true;
                                        errorCode = -2000;
                                    }
                                }
                                //==========================================================================
                                // Close files
                                //==========================================================================
                                groups = repository.getEntityMap().getSize();
                               rsf=rsFile;
                            
                                if (!error) {
                                    repository.close(runScript.isChangeReportDetail(), rsFile, runScript.getName());
                                }
                            } else {
                                System.out.println("##ERROR: SourceDescriptor Names are not Unique.");
                                logger.severe("##ERROR: SourceDescriptor Names are not Unique.");
                                error = true;
                                errorCode = -2300;
                            }
                        } else {
                            System.out.println("##ERROR: Unable to open Oyster outputs.");
                            logger.severe("##ERROR: Unable to open Oyster outputs.");
                            error = true;
                            errorCode = -1000;
                        }
                    } else {
                        System.out.println("##ERROR: Comparator and MatchCodes do not match.");
                        logger.severe("##ERROR: Comparator and MatchCodes do not match.");
                        error = true;
                        errorCode = -2100;
                    }
                } else {
                    System.out.println("##ERROR: Reference Items and Rules do not match.");
                    logger.severe("##ERROR: Reference Items and Rules do not match.");
                    error = true;
                    errorCode = -2200;
                }
            } else {
                System.out.println("##ERROR: Invalid RunScript.");
                logger.severe("##ERROR: Invalid RunScript.");
                error = true;
                errorCode = -1100;
            }
        } catch (Exception ex) {
            Logger.getLogger(OysterMain.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        stopTime = now();

        // get the system stats at the end
        if (stats) {
            System.out.println("System stats at the end");
            logger.severe("System stats at the end");
            systemStats();
        }

        String elapsedTime = "";
        if (startTime != null && stopTime != null) {
            elapsedTime = elapsedTime();
        } else {
            error = true;
        }

        //==========================================================================
        // Output reports and statistics
        //==========================================================================
        if (error) {
            System.out.println("Process ended with Errors! Please check log file: " + logFile.replaceAll("%g", "0"));
            System.out.println("Error Code = " + errorCode);
        } else {
            outputStats(elapsedSecs(startTime, stopTime));
        }
        
        StringBuilder sb = new StringBuilder(100);
        sb.append("Time process started at ")
          .append(startTime)
          .append(System.getProperty("line.separator"));
        sb.append("Time process ended at ")
          .append(stopTime)
          .append(System.getProperty("line.separator"));
        sb.append("Total elapsed time ")
          .append(elapsedTime)
          .append(System.getProperty("line.separator"));
        logger.severe(sb.toString());
        System.out.println(sb.toString());

        // close the logger
        fileHandler.close();
        logger.removeHandler(fileHandler);

        return errorCode;
    }
    
    /**
     *  @param args the command line arguments
     */
    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.A1B60F0A-B237-E234-9F30-096148312461]
    // </editor-fold>
    public static void main (String[] args) {
        final OysterMain oMain = new OysterMain();

        System.out.println("Oyster v." + oMain.getVersion());
        System.out.println();

        // if there are not enough args or there is not a runscript than ask for it
        if (args.length < 2){
            args = new String[4];
            args[0] = "-r";
            args[1] = oMain.getRunScriptName(true);
            args[2] = "-l";
            args[3] = oMain.getLogPath(args[1]);
        } else {
            boolean found = false;
            for (int i = 0; i < args.length; i++){
                if ("-r".equalsIgnoreCase(args[i].trim())){
                    found = true;
                    break;
                }
            }
            
            if (!found){
                args = new String[4];
                args[0] = "-r";
                args[1] = oMain.getRunScriptName(true);
                args[2] = "-l";
                args[3] = oMain.getLogPath(args[1]);
            }
        }
        
        // Set the kill flag to the same folder as the runscript file
        oMain.killFile = (new File(args[1])).getParent() + System.getProperty("file.separator") + "kill.txt";
        
        // create monitor thread
        Timer timer = new Timer("HeapSpaceMonitor", true);
        TimerTask hsmonitor = new TimerTask() {
            @Override
            public void run() {
                // Get current size of heap in bytes
                oMain.kill();
            }
        };
        timer.scheduleAtFixedRate(hsmonitor, 100, 500);
        
        oMain.process(args);
        
        if (oMain.die){
            System.exit(11111);
        }
/*
        // make the screen wait before closing
        System.out.println("Press any key to close.");
        try {
            System.in.skip(Integer.MAX_VALUE);
            System.in.read();
        } catch (IOException ex) {
            ex.printStackTrace();
        }
*/
    }
    
    public void kill() {
        long heapSize = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory();

        // Get maximum size of heap in bytes. The heap cannot grow beyond this size.
        // Any attempt will result in an OutOfMemoryException.
        long heapMaxSize = Runtime.getRuntime().maxMemory();
        long used = (long) (((float) heapSize / heapMaxSize) * 100);
        if (used < 90) {
            counterForMemory = 0;
        }
        
        if (used > 90) {
            counterForMemory++;
            if (counterForMemory >= 6000) {
                System.out.println("WARNING: OYSTER has been using more thann 90% of the max allowed memory for 10 minutes");
            }
        }
        
        File f = new File(killFile);
        if (f.exists() && used > 10) {
            die = true;
        }
    }
}