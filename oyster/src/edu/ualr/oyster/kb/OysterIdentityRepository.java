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

package edu.ualr.oyster.kb;

import edu.ualr.oyster.ErrorFormatter;
import edu.ualr.oyster.OysterExplanationFormatter;
import edu.ualr.oyster.core.OysterAttributes;
import edu.ualr.oyster.core.OysterIDGenerator;
import edu.ualr.oyster.data.ClusterRecord;
import edu.ualr.oyster.data.ClusterRecordSet;
import edu.ualr.oyster.data.OysterIdentityRecord;
import edu.ualr.oyster.data.OysterIdentityRecordMap;
import edu.ualr.oyster.index.Index;
import edu.ualr.oyster.io.IdentityParser;
import edu.ualr.oyster.io.OysterDatabaseWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TimeZone;
import java.util.TreeMap;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Interface to the repository of identities as implemented by the system 
 * Responsibilities:
 * <ul>
 * <li>Allows other objects to request an OysterIdentity object by its unique identifier</li>
 * <li>Allows other objects to update an identity in the repository</li>
 * <li>Allows other objects to insert a new identity into the repository</li>
 * </ul>
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.E661BD2F-F8CF-8072-1B08-D413A1E75070]
// </editor-fold> 
public class OysterIdentityRepository {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.C238A730-F218-1D30-9E10-CB3827AA1A85]
    // </editor-fold> 
    /** The id for the <code>OysterIdentityRepository</code> */
    private String id;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.26ABAB31-637D-F857-30A8-58C9897265B2]
    // </editor-fold> 
    /** */
    private boolean debug = false;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.29DBB15E-96BE-92C0-594E-52CCCD11CC0E]
    // </editor-fold> 
    /** */
    private Logger logger = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.9EA6ABFA-9017-8F35-C6E3-2D36CA30E31A]
    // </editor-fold> 
    /** */
    private FileHandler fileHandler = null;

    /** The <code>ClusterRecord</code> for the <code>OysterIdentityRepository</code> */
    private ClusterRecord identity = null;
    
    /** The <code>EntityMap</code> for the <code>OysterIdentityRepository</code> */
    private static EntityMap entityMap = null;
    
    /** The entitySet for the <code>OysterIdentityRepository</code> */
    private static Set<ClusterRecord> entitySet = new LinkedHashSet<ClusterRecord>();
    
    /** The <code>Index</code> for the <code>OysterIdentityRepository</code> */
    private Index valueIndex = null;
    
    /** The assertMap for the <code>OysterIdentityRepository</code> */
    private HashMap<String, LinkedHashSet<String>> assertMap = new HashMap<String, LinkedHashSet<String>>();
    
    /** The linkMap for the <code>OysterIdentityRepository</code> */
    private static HashMap<String, String> linkMap = null;
    
    /** The ruleMap for the <code>OysterIdentityRepository</code> */
    private static HashMap<String, LinkedHashSet<String>> ruleMap = new HashMap<String, LinkedHashSet<String>>();
    
    /** LinkMap PrintWriter */
    private PrintWriter linkMapWriter = null;
    
    /** Repository PrintWriter */
    private PrintWriter repositoryWriter = null;
    
    /** ValueIndex PrintWriter */
    private PrintWriter indexWriter = null;
    
    /** EntityMap PrintWriter */
    private PrintWriter entityWriter = null;
    
    /** Merge Map PrintWriter */
    private PrintWriter mergeMapWriter = null;
    
    /** ChangeReport PrintWriter */
    private PrintWriter changeReportWriter = null;
    
    /** LinkMap Database Connection */
    private OysterDatabaseWriter linkDatabaseWriter = null;
    /** Repository Database Connection */
    private OysterDatabaseWriter identityDatabaseWriter = null;
    
    /** The <code>OysterIDGenerator</code> for the <code>OysterIdentityRepository</code> */
    private OysterIDGenerator gen = null;
    
    /** Used to hold refIDs that were read in from a previous run */
    private Set<String> inputIDs = new HashSet<String>();
    
    /** The Cluster Distribution for the <code>OysterIdentityRepository</code> */
    private TreeMap<Long, Long> clusterDistribution = new TreeMap<Long, Long>();
    
    /** The refID Lookup for the <code>OysterIdentityRepository</code> */
    private HashMap<String, String> refIDLookup = null;
    
    /** The Oyster Version for the <code>OysterIdentityRepository</code> */
    private String oysterVersion = "";
    
    /** The date for the <code>OysterIdentityRepository</code> */
    private String date = "";
    
    /** The RunScript Name for the <code>OysterIdentityRepository</code> */
    private String runScriptName = "";
    
    /** The modifications for the <code>OysterIdentityRepository</code> */
    private TreeMap<String, ModificationRecord> mods = null;
    
    /** The modification id for the <code>OysterIdentityRepository</code> */
    private String mid = "0000001";

    /** */
    private Set<String> passThruAttributes = null;

    private Set<String> sourceNames = null;
    
    /** The Number of Clusters for the <code>OysterIdentityRepository</code> */
    private int numOfClusters = 0;

    /** The Number of References for the <code>OysterIdentityRepository</code> */
    private int numOfReferences = 0;
    
    private TreeMap<Integer, Integer> candidateList = new TreeMap<Integer, Integer>();
    private TreeMap<Integer, Integer> filteredCandidateList = new TreeMap<Integer, Integer>();
    
    private int newIdentities = 0;
    private int updatedIdentities = 0;
    private int mergedIdentities = 0;
    private int noChangedIdentities = 0;
    private int errorIdentities = 0;
    private int maxChangeReportExamples = 50;
    
    private int slidingWindow = -1;
    
    private boolean traceOn = false;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.6BAA0170-1645-AE25-6DBB-57D2CB430AE2]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>OysterIdentityRepository</code>
     * @param logFile
     * @param logLevel
     * @param attributes
     */
    public OysterIdentityRepository (String logFile, Level logLevel, OysterAttributes attributes, String securityHash, int recordType) {
        try {
            identity = new ClusterRecordSet(recordType);
            identity.createMetaData(attributes);
            
            gen = new OysterIDGenerator(securityHash);
            refIDLookup = new HashMap<String, String>();
            mods = new TreeMap<String, ModificationRecord>();
            
            // initialize logger
            logger = Logger.getLogger(getClass().getName());
            fileHandler = new FileHandler(logFile);
//            consoleHandler = new ConsoleHandler();
            
            // add handlers
            logger.addHandler(fileHandler);
//            logger.addHandler(consoleHandler);
            
            // set level and formatter
            logger.setLevel(logLevel);
            OysterExplanationFormatter formatter = new OysterExplanationFormatter();
            fileHandler.setFormatter(formatter);
        } catch (IOException ex) {
            Logger.getLogger(OysterIdentityRepository.class.getName()).log(Level.SEVERE, null, ex);
        } catch (SecurityException ex) {
            Logger.getLogger(OysterIdentityRepository.class.getName()).log(Level.SEVERE, null, ex);
        }
    }

    /**
     * Creates a new instance of <code>OysterIdentityRepository</code>
     * @param log
     * @param attributes
     * @param securityHash
     */
    public OysterIdentityRepository (Logger log, OysterAttributes attributes, String securityHash, int recordType) {
        try {
            identity = new ClusterRecordSet(recordType);
            identity.createMetaData(attributes);
            
            gen = new OysterIDGenerator(securityHash);
            refIDLookup = new HashMap<String, String>();
            mods = new TreeMap<String, ModificationRecord>();
            
            // initialize logger
            this.logger = log;
        } catch (SecurityException ex) {
            Logger.getLogger(OysterIdentityRepository.class.getName()).log(Level.SEVERE, null, ex);
        }
    }

    public OysterIdentityRepository (int recordType) {
        try {
            identity = new ClusterRecordSet(recordType);
//            identity.creataMetaData(attributes);
            
            gen = new OysterIDGenerator("MD5");
            refIDLookup = new HashMap<String, String>();
            mods = new TreeMap<String, ModificationRecord>();
            
            // initialize logger
            this.logger = Logger.getLogger(getClass().getName());
        } catch (SecurityException ex) {
            Logger.getLogger(OysterIdentityRepository.class.getName()).log(Level.SEVERE, null, ex);
        }
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.2609DB3C-764F-2CBE-5B80-988C0F09E023]
    // </editor-fold> 
    /**
     * Returns the id for this <code>OysterIdentityRepository</code>.
     * @return the id.
     */
    public String getId () {
        return id;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.0F1846B1-14FC-5FF6-8C85-E242B3501CB4]
    // </editor-fold> 
    /**
     * Returns whether the <code>OysterIdentityRepository</code> is in debug mode.
     * @return true if the <code>OysterIdentityRepository</code> is in debug mode, otherwise false.
     */
    public boolean isDebug () {
        return debug;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.18A6952F-ABC4-469D-10BB-FB429135E8DA]
    // </editor-fold> 
    /**
     * Enables/disables debug mode for the <code>OysterIdentityRepository</code>.
     * @param debug true to enable debug mode, false to disable it.
     */
    public void setDebug (boolean debug) {
        this.debug = debug;
    }

    /**
     * Returns the <code>EntityMap</code> for this <code>OysterIdentityRepository</code>.
     * @return the EntityMap
     */
    public EntityMap getEntityMap() {
        return entityMap;
    }

    /**
     * Sets the <code>EntityMap</code> for this <code>OysterIdentityRepository</code>.
     * @param aEntityMap the EntityMap to be set.
     */
    public void setEntityMap(EntityMap aEntityMap) {
        entityMap = aEntityMap;
    }
    
    /**
     * Returns the EntitySet for this <code>OysterIdentityRepository</code>.
     * @return the EntitySet
     */
    public Set<ClusterRecord> getEntitySet() {
        return entitySet;
    }

    /**
     * Sets the EntitySet for this <code>OysterIdentityRepository</code>.
     * @param aEntitySet the EntitySet to be set.
     */
    public void setEntitySet(Set<ClusterRecord> aEntitySet) {
        entitySet = aEntitySet;
    }
    
    /**
     * Returns the LinkMap for this <code>OysterIdentityRepository</code>.
     * @return the LinkMap.
     */
    public HashMap<String, String> getLinkMap() {
        return linkMap;
    }

    /**
     * Sets the LinkMap for this <code>OysterIdentityRepository</code>.
     * @param aLinkMap the LinkMap to be set.
     */
    public void setLinkMap(HashMap<String, String> aLinkMap) {
        linkMap = aLinkMap;
    }
    
    /**
     * Returns the RuleMap for this <code>OysterIdentityRepository</code>.
     * @return the RuleMap.
     */
    public HashMap<String, LinkedHashSet<String>> getRuleMap() {
        return ruleMap;
    }

    /**
     * Sets the RuleMap for this <code>OysterIdentityRepository</code>.
     * @param aRuleMap the RuleMap to be set.
     */
    public void setRuleMap(HashMap<String, LinkedHashSet<String>> aRuleMap) {
        ruleMap = aRuleMap;
    }
    
    /**
     * Returns the ValueIndex for this <code>OysterIdentityRepository</code>.
     * @return the ValueIndex.
     */
    public Index getValueIndex() {
        return valueIndex;
    }
    
    /**
     * Sets the ValueIndex for this <code>OysterIdentityRepository</code>.
     * @param aValueIndex the ValueIndex to be set.
     */
    public void setValueIndex(Index aValueIndex) {
        valueIndex = aValueIndex;
    }
    
    /**
     * Returns the AssertMap for this <code>OysterIdentityRepository</code>. This
     * Contains a map of Assertion IDs to a list of Reference IDs
     * @return the AssertMap.
     */
    public HashMap<String, LinkedHashSet<String>> getAssertMap() {
        return assertMap;
    }
    
    /**
     * Returns the <code>PrintWriter</code> of the Repository for this <code>OysterIdentityRepository</code>.
     * @return the <code>PrintWriter</code>
     */
    public PrintWriter getLinkMapWriter() {
        return linkMapWriter;
    }

    /**
     * Sets the <code>PrintWriter</code> of the Repository for this <code>OysterIdentityRepository</code>.
     * @param linkMapWriter the <code>PrintWriter</code> to be set.
     */
    public void setLinkMapWriter(PrintWriter linkMapWriter) {
        this.linkMapWriter = linkMapWriter;
    }
   
    /**
     * Returns the <code>PrintWriter</code> of the LinkMap for this <code>OysterIdentityRepository</code>.
     * @return the <code>PrintWriter</code>
     */
    public PrintWriter getRepositoryWriter() {
        return repositoryWriter;
    }

    /**
     * Sets the <code>PrintWriter</code> of the LinkMap for this <code>OysterIdentityRepository</code>.
     * @param repositoryWriter the <code>PrintWriter</code> to be set.
     */
    public void setRepositoryWriter(PrintWriter repositoryWriter) {
        this.repositoryWriter = repositoryWriter;
    }

    /**
     * Returns the <code>PrintWriter</code> of the ValueIndex for this <code>OysterIdentityRepository</code>.
     * @return the <code>PrintWriter</code>
     */
    public PrintWriter getIndexWriter() {
        return indexWriter;
    }

    /**
     * Sets the <code>PrintWriter</code> of the ValueIndex for this <code>OysterIdentityRepository</code>.
     * @param indexWriter the <code>PrintWriter</code> to be set.
     */
    public void setIndexWriter(PrintWriter indexWriter) {
        this.indexWriter = indexWriter;
    }

    /**
     * Returns the <code>PrintWriter</code> of the EntityMap for this <code>OysterIdentityRepository</code>.
     * @return the <code>PrintWriter</code>
     */
    public PrintWriter getEntityWriter() {
        return entityWriter;
    }

    /**
     * Sets the <code>PrintWriter</code> of the EntityMap for this <code>OysterIdentityRepository</code>.
     * @param entityWriter the <code>PrintWriter</code> to be set.
     */
    public void setEntityWriter(PrintWriter entityWriter) {
        this.entityWriter = entityWriter;
    }
    
    /**
     * Returns the <code>PrintWriter</code> of the MergeMap for this <code>OysterIdentityRepository</code>.
     * @return the <code>PrintWriter</code>
     */
    public PrintWriter getMergeMapWriter() {
        return mergeMapWriter;
    }

    /**
     * Sets the <code>PrintWriter</code> of the MergeMap for this <code>OysterIdentityRepository</code>.
     * @param mergeMapWriter the <code>PrintWriter</code> to be set.
     */
    public void setMergeMapWriter(PrintWriter mergeMapWriter) {
        this.mergeMapWriter = mergeMapWriter;
    }
    
    /**
     * Returns the <code>PrintWriter</code> of the ChangeReport for this <code>OysterIdentityRepository</code>.
     * @return the <code>PrintWriter</code>
     */
    public PrintWriter getChangeReportWriter() {
        return changeReportWriter;
    }

    /**
     * Sets the <code>PrintWriter</code> of the ChangeReport for this <code>OysterIdentityRepository</code>.
     * @param changeReportWriter the <code>PrintWriter</code> to be set.
     */
    public void setChangeReportWriter(PrintWriter changeReportWriter) {
        this.changeReportWriter = changeReportWriter;
    }

    /**
     * Returns the Link <code>OysterDatabaseWriter</code> of the Repository for this <code>OysterIdentityRepository</code>.
     * @return the <code>OysterDatabaseWriter</code>
     */
    public OysterDatabaseWriter getLinkDatabaseWriter() {
        return linkDatabaseWriter;
    }

    /**
     * Sets the Link <code>OysterDatabaseWriter</code> of the Repository for this <code>OysterIdentityRepository</code>.
     * @param linkDatabaseWriter the <code>OysterDatabaseWriter</code> to be set.
     */
    public void setLinkDatabaseWriter(OysterDatabaseWriter linkDatabaseWriter) {
        this.linkDatabaseWriter = linkDatabaseWriter;
    }
    
    /**
     * Returns the Identity <code>OysterDatabaseWriter</code> of the Repository for this <code>OysterIdentityRepository</code>.
     * @return the <code>OysterDatabaseWriter</code>
     */
    public OysterDatabaseWriter getIdentityDatabaseWriter() {
        return identityDatabaseWriter;
    }

    /**
     * Sets the Identity <code>OysterDatabaseWriter</code> of the Repository for this <code>OysterIdentityRepository</code>.
     * @param identityDatabaseWriter the <code>OysterDatabaseWriter</code> to be set.
     */
    public void setIdentityDatabaseWriter(OysterDatabaseWriter identityDatabaseWriter) {
        this.identityDatabaseWriter = identityDatabaseWriter;
    }

    /**
     * Returns the Cluster Distribution for this <code>OysterIdentityRepository</code>.
     * @return the cluster distribution
     */
    public TreeMap<Long, Long> getClusterDistribution() {
        return clusterDistribution;
    }
    
    /**
     * Returns the RefID Lookup for this <code>OysterIdentityRepository</code>.
     * @return the refid
     */
    public HashMap<String, String> getRefIDLookup() {
        return refIDLookup;
    }
    
    /**
     * Returns the Oyster Version for this <code>OysterIdentityRepository</code>.
     * @return the oyster version
     */
    public String getOysterVersion() {
        return oysterVersion;
    }

    /**
     * Sets the Oyster Version for this <code>OysterIdentityRepository</code>.
     * @param oysterVersion the oyster version to be set
     */
    public void setOysterVersion(String oysterVersion) {
        this.oysterVersion = oysterVersion;
    }

    /**
     * Returns the date for this <code>OysterIdentityRepository</code>.
     * @return the date
     */
    public String getDate() {
        return date;
    }

    /** 
     * Sets the date for this <code>OysterIdentityRepository</code>.
     * @param date the date to be set
     */
    public void setDate(String date) {
        this.date = date;
    }

    /**
     * Returns the RunScript Name for this <code>OysterIdentityRepository</code>.
     * @return the runscript name
     */
    public String getRunScriptName() {
        return runScriptName;
    }

    /**
     * Sets the RunScript Name for this <code>OysterIdentityRepository</code>.
     * @param runScriptName the runscript name to be set
     */
    public void setRunScriptName(String runScriptName) {
        this.runScriptName = runScriptName;
    }

    /**
     * Returns the Modifications for this <code>OysterIdentityRepository</code>.
     * @return the current modifications
     */
    public TreeMap<String, ModificationRecord> getMods() {
        return mods;
    }

    /**
     * Sets the Modifications for this <code>OysterIdentityRepository</code>.
     * @param mods modifications to be set
     */
    public void setMods(TreeMap<String, ModificationRecord> mods) {
        this.mods = mods;
    }

    /**
     * Returns the Modification ID for this <code>OysterIdentityRepository</code>.
     * @return the current modification id
     */
    public String getMid() {
        return mid;
    }

    /**
     * Sets the Modification ID for this <code>OysterIdentityRepository</code>.
     * @param mid modification id to be set
     */
    public void setMid(String mid) {
        this.mid = mid;
    }

    public Set<String> getPassThruAttributes() {
        return passThruAttributes;
    }

    public void setPassThruAttributes(Set<String> passThruAttributes) {
        if (passThruAttributes == null) {
            this.passThruAttributes = new HashSet<String>();
        } else {
            this.passThruAttributes = passThruAttributes;
        }
    }
    
    /**
     * Returns the Number of Clusters for this <code>OysterIdentityRepository</code>.
     * @return the number of clusters
     */
    public int getNumOfClusters() {
        return numOfClusters;
    }

    /** 
     * Returns the Number of References for this <code>OysterIdentityRepository</code>.
     * @return the number of references
     */
    public int getNumOfReferences() {
        return numOfReferences;
    }

    public int getMaxChangeReportExamples() {
        return maxChangeReportExamples;
    }

    public void setMaxChangeReportExamples(int maxChangeReportExamples) {
        this.maxChangeReportExamples = maxChangeReportExamples;
    }

    public int getSlidingWindow() {
        return slidingWindow;
    }

    public void setSlidingWindow(int slidingWindow) {
        this.slidingWindow = slidingWindow;
    }

    public boolean isTraceOn() {
        return traceOn;
    }

    public void setTraceOn(boolean traceOn) {
        this.traceOn = traceOn;
    }

    public int getNewIdentities() {
        return newIdentities;
    }

    public void setNewIdentities(int newIdentities) {
        this.newIdentities = newIdentities;
    }

    public int getUpdatedIdentities() {
        return updatedIdentities;
    }

    public void setUpdatedIdentities(int updatedIdentities) {
        this.updatedIdentities = updatedIdentities;
    }

    public int getMergedIdentities() {
        return mergedIdentities;
    }

    public void setMergedIdentities(int mergedIdentities) {
        this.mergedIdentities = mergedIdentities;
    }

    public int getNoChangedIdentities() {
        return noChangedIdentities;
    }

    public void setNoChangedIdentities(int noChangedIdentities) {
        this.noChangedIdentities = noChangedIdentities;
    }

    public Set<String> getSourceNames() {
        return sourceNames;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.E8D16456-CA3E-30B6-27F2-ECAB1053ACFD]
    // </editor-fold> 
    /**
     * This method adds a new identity to the entityMap.
     * @param oysterId system generated OysterID.
     * @param oir <code>OysterIdentityRecord</code> to be added.
     */
    public void addNewIdentity (String oysterId, OysterIdentityRecord oir) {
        Set<String> set = new LinkedHashSet<String>();
        set.add("@");
        entityMap.addIdentity(oysterId, oir, mid, set, traceOn);
    }

    /**
     * This method adds a new identity to the entityMap.
     * @param oysterId system generated OysterID.
     * @param cr <code>ClusterRecord</code> to be added.
     */
    public void addNewIdentity (String oysterId, ClusterRecord cr) {
        Set<String> set = new LinkedHashSet<String>();
        set.add("@");
        entityMap.addIdentity(oysterId, cr, mid, set, traceOn);
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.B778D4E1-E4F7-4056-3603-206D359E40EC]
    // </editor-fold> 
    /**
     * This method takes the new <code>ClusterRecord</code> and merges it with
     * the old <code>ClusterRecord</code> then replaces the old <code>
     * ClusterRecord</code> in the entityMap with the merged one. This allows 
     * any new information to be kept with the old.
     * @param oysterId the index into the entityMap.
     * @param cr <code>ClusterRecord</code> to be updated.
     */
    public void updateIdentity (String oysterId, ClusterRecord cr) {
        LinkedHashSet<String> set = ruleMap.get(oysterId);
        entityMap.updateIdentity(oysterId, cr, mid, set, traceOn);
    }

    /**
     * This method takes the new <code>ClusterRecord</code> and merges it with 
     * the old <code>ClusterRecord</code> then replaces the old <code>
     * ClusterRecord</code> in the entityMap with the merged one. This allows 
     * any new information to be kept with the old.
     * 
     * Rules for determining the persistence of the OysterID.
     * 1. An input record is read that matches another input record but neither 
     *    record matches a knowledgebase record. The new cluster is assigned the
     *    minimum OysterID value between their two OysterIDs.
     * 2. An input record is read that matches a knowledgebase record. The 
     *    updated cluster retains the knowledgebase OysterID for that cluster.
     * 3. Two knowledgebase clusters merge because of the addition of new 
     *    information from the new source. The merged cluster is assigned the 
     *    oldest OysterID. If both clusters have the same creation data then the
     *    minimum OysterID value between their two OysterIDs is taken.
     * 4. (This happens because of R-Swoosh) If the input record is Persistent 
     *    then take then take the input OysterID. The only reason this is an 
     *    input record is because R-Swoosh takes a record that it has already 
     *    seen and puts it on the bottom of the input queue. 
     *
     * @param input the <code>ClusterRecord</code> to be merged.
     * @param cr <code>ClusterRecord</code> to be updated.
     * @param OysterID 
     * @param rule the rules that fired for the current oysterID.
     * @return minimum OysterID
     */
    public String updateEntitySet (ClusterRecord input, ClusterRecord cr, String OysterID, Set<String> rule) {
        String minOysterID;
        
        if (cr != null){
            // deterimine persistance of the OysterID
            minOysterID = getMinOysterID(input, cr);
            
            String refID = cr.getValuesByAttribute("@RefID");
            if (!inputIDs.contains(refID)){
                if (input != null){
                    if (minOysterID.equals(cr.getOysterID())){
                        cr.merge(input.clone(), mid, rule, traceOn);
                        cr.setOysterID(minOysterID);
                        entitySet.add(cr);
                    } else {
                        input.merge(cr, mid, rule, traceOn);
                        input.setOysterID(minOysterID);
                        entitySet.add(input);
                    }
                }
            } else {
                // create a new ClusterRecord insert all the data except for the RefID
                ClusterRecord cr2 = cr.clone();

                // FIXME: This was removed for bug #18. Why was it ever used?
//                cr2.removeField("@RefID");
                // which is the min cluster
                String clusterID = this.getMinOysterID(input, cr2);
                if (clusterID.equals(cr2.getOysterID())){
                    cr2.merge(input.clone(), mid, rule, traceOn);
                    
                    cr2.setOysterID(minOysterID);
                    entitySet.add(cr2);
                } else{
                    input.merge(cr2.clone(), mid, rule, traceOn);

                    input.setOysterID(minOysterID);
                    entitySet.add(input);
                }
            }
        } else {
            input.setOysterID(OysterID);
            entitySet.add(input);
            minOysterID = OysterID;
        }
        
        return minOysterID;
    }
    
    public String getMinOysterID(ClusterRecord input, ClusterRecord cr) {
        String minOysterID = null;
        if (input == null && cr == null) {
            
        } else if (input == null && cr != null) {
            minOysterID = cr.getOysterID();
        } else if (input != null && cr == null) {
            minOysterID = input.getOysterID();
        } else {
            if (!cr.isPersistant() && !input.isPersistant()) {
                if (input.getOysterID() == null) {
                    minOysterID = cr.getOysterID();
                } else if (cr.getOysterID().hashCode() < input.getOysterID().hashCode()) {
                    minOysterID = cr.getOysterID();
                } else {
                    minOysterID = input.getOysterID();
                }
            } else if (cr.isPersistant() && !input.isPersistant()) {
                minOysterID = cr.getOysterID();
            } else if (!cr.isPersistant() && input.isPersistant()) {
                minOysterID = input.getOysterID();
            } else if (cr.isPersistant() && input.isPersistant()) {
                if (cr.getCreationDate().equals(input.getCreationDate())) {
                    if (cr.getOysterID().hashCode() < input.getOysterID().hashCode()) {
                        minOysterID = cr.getOysterID();
                    } else {
                        minOysterID = input.getOysterID();
                    }
                } else if (cr.getCreationDate().before(input.getCreationDate())) {
                    minOysterID = cr.getOysterID();
                } else {
                    minOysterID = input.getOysterID();
                }
            }
        }
        return minOysterID;
    }
    
    /**
     * Adds a new <code>OysterIdentityRecord</code> to the valueIndex.
     * @param oysterIdentityRecord the <code>OysterIdentityRecord</code> to be set.
     */
    public void addIndex(OysterIdentityRecord oysterIdentityRecord){
        valueIndex.addEntry(oysterIdentityRecord);
    }
    
    /**
     * Adds a new <code>OysterIdentityRecord</code> to the valueIndex.
     * @param index the index value to set the <code>OysterIdentityRecord</code> to.
     * @param oysterIdentityRecord the <code>OysterIdentityRecord</code> to be set.
     */
    public void addIndex(String index, OysterIdentityRecord oysterIdentityRecord){
        valueIndex.addEntry(index, oysterIdentityRecord);
    }
    
    /**
     * Adds a new <code>ClusterRecord</code> to the valueIndex.
     * @param clusterRecord the <code>ClusterRecord</code> to be set.
     * @param mergedList true if the merged record is to be used otherwise false
     */
    public void addIndex(ClusterRecord clusterRecord, boolean mergedList){
        if (mergedList){
            // create all possible (shadow) records
            ClusterRecord cr = cartesianProduct(clusterRecord);
            for (int i = 0; i < cr.getSize(); i++) {
                OysterIdentityRecord oir = cr.getOysterIdentityRecord(i);
                valueIndex.addEntry(oir);
            }
        } else {
            for (int i = 0; i < clusterRecord.getSize(); i++) {
                OysterIdentityRecord oir = clusterRecord.getOysterIdentityRecord(i);
                valueIndex.addEntry(oir);
            }
        }
    }
    
    /**
     * Removes the refID from the index based on the <code>OysterIdentityRecord
     * </code> data.
     * @param oir the <code>OysterIdentityRecord</code> to be checked for the refID
     * @param refID the refID to remove.
     */
    public void removeIndex(OysterIdentityRecord oir, String refID) {
        valueIndex.removeEntry(oir, refID);
    }
    
    /**
     * Adds the Reference Id and OysterId to the linkMap.
     * @param oysterIdentityRecord the <code>OysterIdentityRecord</code> 
     * containing the refID to be added.
     * @param id the system generated OysterID to be added.
     * @param rule the rule that brought this record into the linkMap, empty if 
     * this is the first record in an Oyster grouping
     */
    public void addLink(OysterIdentityRecord oysterIdentityRecord, String id, String rule) {
        String refIDs = oysterIdentityRecord.get("@RefID");
        String [] refID = refIDs.split("[|]");

        boolean containsSelfRef = doesContainsSelfRef(refID);

        for (int i = 0; i < refID.length; i++){
            if (!inputIDs.contains(refID[i])){
                linkMap.put(refID[i], id);
                
                if (rule != null && !rule.equals("")){
                    LinkedHashSet<String> s = ruleMap.get(refID[i]);
                    if (s == null) {
                        s = new LinkedHashSet<String>();
                    }
                    s.add(rule);
                    ruleMap.put(refID[i], s);
                } else if (!containsSelfRef){
                    LinkedHashSet<String> s = ruleMap.get(refID[i]);
                    if (s == null) {
                        s = new LinkedHashSet<String>();
                    }
                    s.add("@");
                    ruleMap.put(refID[i], s);
                }
            }
        }
    }

    /**
     * Checks to see if this list of reference ids contains a self reference
     * @param refID the id's to check
     * @return true if this ref id list contains a self reference, otherwise false
     */
    private boolean doesContainsSelfRef(String[] refID) {
        boolean flag = false;
        for (int i = 0; i < refID.length; i++){
            LinkedHashSet<String> s = ruleMap.get(refID[i]);
            
            if (s != null && s.contains("@")){
                flag = true;
                break;
            }
        }
        return flag;
    }
    
    /**
     * Updates the OysterID for a particular Reference Id in the linkMap.
     * @param refID the reference id to be updated.
     * @param oysterID the system generated OysterID to be added.
     * @param rule the rule that brought this record into the linkMap, empty if 
     * this is the first record in an Oyster grouping
     */
    public void updateLink(String refID, String oysterID, String rule, String newID){
        if (refID != null && !inputIDs.contains(refID)){
            linkMap.put(refID, oysterID);
                
            if (rule != null && !rule.equals("")){
                LinkedHashSet<String> s = ruleMap.get(refID);
                if (s == null) {
                    s = new LinkedHashSet<String>();
                }
                s.add(rule);
                ruleMap.put(refID, s);
            }
        } else {
            linkMap.put(newID, oysterID);
                
            if (rule != null && !rule.equals("")){
                LinkedHashSet<String> s = ruleMap.get(newID);
                if (s == null) {
                    s = new LinkedHashSet<String>();
                }
                s.add(rule);
                ruleMap.put(newID, s);
            }
        }
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.2FB8B304-8955-9339-FF50-EBAB2A16E455]
    // </editor-fold> 
    /**
     * Returns the next OysterID.
     * @param oir the <code>OysterIdentityRecord</code> used to create the OysterID.
     * @param derived
     * @return id the OysterID.
     */
    public String getNextID (OysterIdentityRecord oir, boolean derived) {
        id = gen.getOysterID(oir, derived, passThruAttributes);
        return id;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.41E3AC7A-FDE0-10D5-3B99-E084358E6870]
    // </editor-fold> 
    /**
     * The method returns a list of possible candidates to be matched against by
     * the ER engine. It takes the <code>ClusterRecord</code> and compares it
     * to the index. If the sorted option is selected, then the list is sorted
     * in descending order based on the number of elements in the record that 
     * matched to the index. This list is then filter by the least common rule 
     * denominator list to remove any records that would never pass. These are 
     * usually records that match on a single non-restricting element.
     * @param clusterRecord the <code>ClusterRecord</code> to be searched for.
     * @param sort true to sort the list, otherwise false.
     * @param lcrd the least common rule denominator list to use as a filter.
     * @param lcrdMinSize the smallest size match that will be allowed to search
     * the filter.
     * @param bypassFilter true if the filter is to be bypassed otherwise false.
     * @param mergedList
     * @return a map of RefID's and <code>ClusterRecord</code> that matched.
     */
    @SuppressWarnings( "unchecked" )
    public Map<String, ClusterRecord> getCandidateList(ClusterRecord clusterRecord, boolean sort, Map<Integer, ArrayList<String>> lcrd, int lcrdMinSize, boolean bypassFilter, boolean mergedList) {
        Map<String, ClusterRecord> result = new LinkedHashMap<String, ClusterRecord>();
        Map<String, ClusterRecord> candidates = new LinkedHashMap<String, ClusterRecord>();
        OysterIdentityRecord oysterIdentityRecord = clusterRecord.getMergedRecord();
        int list, flist;

        Set<String> s;
        if (mergedList) {
            ClusterRecord cr = new ClusterRecordSet(clusterRecord.getRecordType());
            cr.insertRecord(oysterIdentityRecord);
            s = valueIndex.getCandidateList(cartesianProduct(cr), lcrd, mergedList);
        } else {
            s = valueIndex.getCandidateList(clusterRecord, lcrd, mergedList);
        }

        for (Iterator<String> it = s.iterator(); it.hasNext();) {
            String refID = it.next();
            String oysterID = linkMap.get(refID);
            if (oysterID == null) {
                oysterID = getRefIDLookup().get(refID);
            }
            ClusterRecord cr = entityMap.getCluster(oysterID);

            if (cr != null) {
                for (int i = 0; i < cr.getSize(); i++) {
                    OysterIdentityRecord oir = cr.getOysterIdentityRecord(i);

                    if (oir.get("@RefID").equals(refID)) {
                        ClusterRecord c = new ClusterRecordSet(cr.getRecordType());
                        c.insertRecord(oir, false);
                        candidates.put(refID, c);
                        break;
                    }
                }
            } else {
//                    System.out.println("Null CR for refID: " + refID + " oysterID: " + oysterID);
            }
        }

        // now filter
        for (Iterator<String> it = candidates.keySet().iterator(); it.hasNext();) {
            String refID = it.next();
            ClusterRecord cr = candidates.get(refID);
            if (cr != null) {
                // ensure the cr matches at least the lcrd filter
                if (bypassFilter) {
                    String oysterID = linkMap.get(refID);

                    if (oysterID == null) {
                        oysterID = refIDLookup.get(refID);
                    }

                    if (oysterID != null) {
                        cr = entityMap.getCluster(oysterID);
                    }

                    if (cr != null) {
                        result.put(refID, cr);
                    }
                } else {
                    if (filter(cr, oysterIdentityRecord, lcrd)) {
                        cr = null;
                        String oysterID = linkMap.get(refID);

                        if (oysterID == null) {
                            oysterID = refIDLookup.get(refID);
                        }

                        if (oysterID != null) {
                            cr = entityMap.getCluster(oysterID);
                        }

                        if (cr != null) {
                            result.put(refID, cr);
                        }
                    }
                }
            }
        }

        list = candidates.size();
        flist = result.size();

        /*        
         if (this.debug){
         System.out.println("## List Size       : " + list);
         System.out.println("## Filter List Size: " + flist);
         }
         */
        int value = 0;
        if (filteredCandidateList.containsKey(flist)) {
            value = filteredCandidateList.get(flist);
        }
        value++;
        filteredCandidateList.put(flist, value);

        value = 0;
        if (candidateList.containsKey(list)) {
            value = candidateList.get(list);
        }
        value++;
        candidateList.put(list, value);

        return result;
    }

    private int getRecordIDNumber(String refID){
        int result;
        String temp = refID;
        
        // remove the source name
        int dot;
        if ((dot = temp.lastIndexOf(".")) != -1){
            temp = temp.substring(dot+1);
        }
        
        temp = temp.replaceAll("\\D", "");
        
        result = Integer.parseInt(temp);
        return result;
    }
    
    /**
     * The method returns a list of possible candidates to be matched against by
     * the ER engine.
     * @param clusterRecord the <code>ClusterRecord</code> to be searched for.
     * @param assertionType the Assertion type to be pulled.
     * @return a map of RefID's and <code>ClusterRecord</code> that matched.
     */
    public Map<String, ClusterRecord> getAssertionList(ClusterRecord clusterRecord, String assertionType) {
        Map<String, ClusterRecord> result = new LinkedHashMap<String, ClusterRecord>();
        
        LinkedHashSet<String> s = assertMap.get(clusterRecord.getMergedRecord().get(assertionType));
/*
        if (s == null)
            s = assertMap.get(clusterRecord.getMergedRecord().get("@AbsAssert"));
*/
        if (s != null){
            for (Iterator<String> it = s.iterator(); it.hasNext();){
                String refID = it.next();
                
                String oysterID = linkMap.get(refID);
                
                if (oysterID == null) {
                    oysterID = refIDLookup.get(refID);
                }
                
                if (oysterID != null){
                    ClusterRecord cr = entityMap.getCluster(oysterID);
                    if (cr != null) {
                        result.put(refID, cr);
                    }
                }
            }
        }
        
        return result;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.E4FDCF99-FED4-C3D8-3262-169E520297AD]
    // </editor-fold> 
    /**
     * This method closes the repository.
     */
    @SuppressWarnings( "unchecked" )
    public void close (boolean changeReportDetail, String rsFile, String runScriptName) {
        if (logger.isLoggable(Level.INFO)) {
            StringBuilder sb = new StringBuilder(1000);
            
            // Output Candidate List Frequencies;
            sb.append("Filtered Candidate List Frequencies")
              .append(System.getProperty("line.separator"));
            for (Iterator<Integer> it = filteredCandidateList.keySet().iterator(); it.hasNext();) {
                int key = it.next();
                int value = filteredCandidateList.get(key);
                sb.append(key).append("\t").append(value)
                  .append(System.getProperty("line.separator"));
            }
            sb.append(System.getProperty("line.separator"));
            sb.append(System.getProperty("line.separator"));

            sb.append("UnFiltered Candidate List Frequencies")
              .append(System.getProperty("line.separator"));
            for (Iterator<Integer> it = candidateList.keySet().iterator(); it.hasNext();) {
                int key = it.next();
                int value = candidateList.get(key);
                sb.append(key).append("\t").append(value)
                  .append(System.getProperty("line.separator"));
            }
            sb.append(System.getProperty("line.separator"));
            sb.append(System.getProperty("line.separator"));
            logger.severe(sb.toString());
        }

        if (linkMapWriter != null) {
            outputLinkMap();
        } else if (linkDatabaseWriter != null) {
            linkDatabaseWriter.loadLink(linkMap, ruleMap);
        }
        
        if(repositoryWriter != null) {
            outputRepository(false);
        } else if (identityDatabaseWriter != null) {
            ;
        }
        
        if (debug){
            outputValueIndex();
            outputEntityMap();
        }
        
        // check to see if trace is set if not this doesn't matter
        if (this.traceOn){
        outputChangeDetailReport(changeReportDetail, rsFile, runScriptName);
        
            if(mergeMapWriter != null) {
                outputMergeMap();
                mergeMapWriter.close();
            }
            
            changeReportWriter.close();
        }
        
        // close the PrintWriters.
        if(linkMapWriter != null) {
            linkMapWriter.close();
        }
        
        if(repositoryWriter != null) {
            repositoryWriter.close();
        }
        
        if(indexWriter != null) {
            indexWriter.close();
        }
        
        if(entityWriter != null) {
            entityWriter.close();
        }
        
        // close the Database Connections.
        if(linkDatabaseWriter != null) {
            linkDatabaseWriter.close();
        }
        
        if(identityDatabaseWriter != null) {
            identityDatabaseWriter.close();
        }
        
        // release the memory
        identity = null;
        valueIndex = null;
        linkMap = null;
        entityMap.close();
        entityMap = null;
    }
    
    /**
     * This method loads a previously run Identity.xml file into memory.
     * @param file the Identity.xml file to be loaded.
     * @param keepPreviousDBTable true to keep the previously loaded DB tables.
     */
    public void load(String file, boolean keepPreviousDBTable, boolean trace){
        System.out.println();
        
        StringBuilder sb = new StringBuilder(100);
        sb.append("Loading Previous IdentityRepository: ").append(file);
        System.out.println(sb.toString());
        logger.severe(sb.toString());
        
        IdentityParser iParser = new IdentityParser(identity.getRecordType());
        iParser.setTraceOn(trace);
        
        if (keepPreviousDBTable && entityMap.getClass().getSimpleName().equalsIgnoreCase("DBEntityMap")) {
            iParser.setDontLoad(true);
        }
        
        if (entityMap.getClass().getSimpleName().equalsIgnoreCase("DBEntityMap")) {
            try {
                ((DBEntityMap) entityMap).getConn().setAutoCommit(false);
            } catch (SQLException ex) {
                Logger.getLogger(OysterIdentityRepository.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
            }
        }
        
        iParser.parse(file, valueIndex, entityMap);
        entityMap = iParser.getEntityMap();
        linkMap = iParser.getLinkMap();
        inputIDs = iParser.getInputIDs();
        refIDLookup =  iParser.getRefIDLookup();
        mods = iParser.getModifications();
        
        numOfClusters = iParser.getClusterCount();
        numOfReferences = iParser.getReferenceCount();
        
        sourceNames = iParser.getSourceNames();
        
        if (entityMap.getClass().getSimpleName().equalsIgnoreCase("DBEntityMap")) {
            try {
                ((DBEntityMap) entityMap).getConn().commit();
                ((DBEntityMap) entityMap).getConn().setAutoCommit(true);
            } catch (SQLException ex) {
                Logger.getLogger(OysterIdentityRepository.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
            }
        }
        
        sb = new StringBuilder(100);
        sb.append("Number of clusters read: ")
          .append(numOfClusters)
          .append(System.getProperty("line.separator"));
        sb.append("Number of references   : ")
          .append(numOfReferences);
        logger.severe(sb.toString());
    }
    
    /**
     * This method checks to see if the <code>ClusterRecord</code> passes at 
     * least one partial rule contained within the Least Common Rule Denominator.
     * If a match is found will return true, otherwise false.
     * @param coDoSAIdentity the <code>ClusterRecord</code> to be checked.
     * @param referenceItems the <code>OysterIdentityRecord</code> to check against.
     * @param lcrd the filter to be used.
     * @return true if the <code>ClusterRecord</code> passes the filter, otherwise false.
     */
    private boolean filter(ClusterRecord cr, OysterIdentityRecord oir, Map<Integer, ArrayList<String>> lcrd) {
        boolean flag = true;

        // iterate over each filter only one needs to pass, i.e OR statement
        for (Iterator<Integer> it = lcrd.keySet().iterator(); it.hasNext();) {
            int key = it.next();
            ArrayList<String> filter = lcrd.get(key);

            // for each rule the answer is initially true
            flag = true;

            boolean[] check = new boolean[filter.size()];
            Arrays.fill(check, false);
            int count = 0;
            // iterate over each filter element EACH one must pass, i.e AND statement
            for (Iterator<String> it2 = filter.iterator(); it2.hasNext();) {
                String field = it2.next();

                String ci = cr.getValuesByAttribute(field);
                String ri = oir.get(field);

                if (ci == null) {
                    check[count] = false;
                } else if (ri == null) {
                    check[count] = false;
                } else {
                    String[] ciArr = ci.split("[|]");

                    for (int i = 0; i < ciArr.length; i++) {
                        if (ri.toUpperCase(Locale.US).indexOf(ciArr[i].toUpperCase(Locale.US)) != -1 && !ciArr[i].equals("")) {
                            check[count] = true;
                            break;
                        }
                    }

                    // check to see if AND failed if so go to next rule
                    if (!check[count]) {
                        flag = false;
                        break;
                    }
                }
                count++;
            }

            // did every element in the current filter pass?
            if (!flag) {
                for (int i = 0; i < check.length; i++) {
                    if (!check[i]) {
                        flag = false;
                        break;
                    }
                }
            }

            if (flag) {
                break;
            }
        }
        return flag;
    }

    /**
     * Returns the system time at a specific point in time
     * @return the time as a string
     */
    private String now(){
        String result;
        /* Get system time & date */
        String DATE_FORMAT = "MMM dd, yyyy";
        java.text.SimpleDateFormat sdf = new java.text.SimpleDateFormat(DATE_FORMAT);
        sdf.setTimeZone(TimeZone.getDefault());
        Calendar cal = Calendar.getInstance(TimeZone.getDefault());

        result = sdf.format(cal.getTime());
        return result;
    }
    
    /**
     * This method writes out the LinkMap in a tab delimited format to a file. 
     * The file name is contained in the RunScript.xml file (and in the <code>
     * RunScript</code>Object).
     */
    public synchronized void outputLinkMap() {
        linkMapWriter.println("RefID\tOysterID\tRule");
        Map<String, Long> clusters = new LinkedHashMap<String, Long>();
        
        for (Iterator<String> it = linkMap.keySet().iterator(); it.hasNext();) {
            String key = it.next();
            String value = linkMap.get(key);
            LinkedHashSet<String> s = ruleMap.get(key);
            
            long count = 0;
            if (clusters.containsKey(value)) {
                count = clusters.get(value);
            }
            count++;
            clusters.put(value, count);
            
            linkMapWriter.println(key + "\t" + value + "\t" + s);
        }
        
        for (Iterator<Entry<String, Long>> it = clusters.entrySet().iterator(); it.hasNext();) {
            Entry<String, Long> entry = it.next();
            long value = entry.getValue();
            
            long count = 0;
            if (clusterDistribution.containsKey(value)) {
                count = clusterDistribution.get(value);
            }
            count++;
            clusterDistribution.put(value, count);
        }
    }

    /**
     * This method writes out the Repository in XML format to a file. The file 
     * name is contained in the RunScript.xml file (and in the <code>RunScript
     * </code>Object).
     */
    public synchronized void outputRepository(boolean skipCurrentMod) {
        Map<String, Integer> m = new LinkedHashMap<String, Integer>();
        // TODO: Change String Operation to an XML Encoding Operation http://www.odi.ch/prog/design/newbies.php#6
        repositoryWriter.println("<?xml version=\"1.0\" encoding=\"UTF-8\"?>");
        repositoryWriter.println("<root>");
        // output metadata
        repositoryWriter.println("\t<Metadata>");
        repositoryWriter.println("\t\t<Modifications>");

        if (!skipCurrentMod) {
            for (Iterator<Entry<String, ModificationRecord>> it = mods.entrySet().iterator(); it.hasNext();) {
                Entry<String, ModificationRecord> entry = it.next();
                ModificationRecord mr = entry.getValue();
                repositoryWriter.println("\t\t\t<Modification ID=\"" + mr.getId() + "\" OysterVersion=\"" + mr.getOysterVersion() + 
                        "\" Date=\"" + mr.getDate() + "\" RunScript=\"" +  mr.getRunScriptName() +"\" />");
            }
        }
        repositoryWriter.println("\t\t\t<Modification ID=\"" + mid + "\" OysterVersion=\"" + oysterVersion + 
                "\" Date=\"" + date + "\" RunScript=\"" + runScriptName + "\" />");
        repositoryWriter.println("\t\t</Modifications>");

        // output attributes
        repositoryWriter.println("\t\t<Attributes>");
        for (Iterator<Entry<String, String>> it = ClusterRecord.getMetadata().entrySet().iterator(); it.hasNext();) {
            Entry<String, String> entry = it.next();

            if (!entry.getValue().startsWith("@") || entry.getValue().equals("@RefID") || entry.getValue().equals("@DupRefID")) {
                repositoryWriter.println("\t\t\t<Attribute Name=\"" + entry.getValue() + "\" Tag=\"" + entry.getKey() + "\"/>");
            }
        }
        repositoryWriter.println("\t\t</Attributes>");
        repositoryWriter.println("\t</Metadata>");

        repositoryWriter.println("\t<Identities>");

        String[] entities = new String[entityMap.getSize()];
        List<String> keys = entityMap.getKeys(entities);
        Collections.sort(keys);
        for (Iterator<String> it = keys.iterator(); it.hasNext();) {
            String key = it.next();
            ClusterRecord cr = entityMap.getCluster(key);
            repositoryWriter.println(cr.convertToXML(date.substring(0, 10)));

            // check to see if trace is set if not this doesn't matter
            if (this.traceOn) {
                // is the record new, updated, merged, or no change
                //FIXME: Change to use switch strings in java 1.7
                char state = 'þ';
                String temp = cr.determineClusterState();
                if (temp.isEmpty()) {
                    System.err.println("WARNING: Unknown Cluster State for Cluster: " + cr.getOysterID());
                } else {
                    state = temp.charAt(0);
                }

                int value = 0;
                if (m.containsKey(String.valueOf(state))) {
                    value = m.get(String.valueOf(state));
                }
                value++;
                m.put(String.valueOf(state), value);

                switch (state) {
                    case 'N':
                        newIdentities++;
                        break;
                    case 'U':
                        updatedIdentities++;
                        break;
                    case 'M':
                        mergedIdentities++;
                        break;
                    case 'X':
                        noChangedIdentities++;
                        break;
                    default:
                        errorIdentities++;
                        System.out.println(cr.toString());
                        System.out.println();
                        break;
                }
            }
        }

        repositoryWriter.println("\t</Identities>");
        repositoryWriter.println("</root>");
    }

    /**
     * This method writes out the ValueIndex in tab delimited format to a file. 
     * The file name is based on the Identity filename contained in the 
     * RunScript.xml file (and in the <code>RunScript</code>Object).
     */
    @SuppressWarnings( "unchecked" )
    private synchronized void outputValueIndex() {
        indexWriter.println("Data Value\tRefID(s)");
        
        if (valueIndex.getClass().getSimpleName().equals("DBIndex")){
            
        } else {
            for (Iterator<String> it = valueIndex.getIterator(); it.hasNext();) {
                String key = it.next();
                Set<String> s = (Set<String>) valueIndex.get(key);
                indexWriter.println(key + "\t" + s);
            }
        }
    }
    
    /**
     * This method writes out the EntityMap in tab delimited format to a file. 
     * The file name is based on the Identity filename contained in the 
     * RunScript.xml file (and in the <code>RunScript</code>Object).
     */
    private synchronized void outputEntityMap() {
        // output CoDoSA Metadata first
        entityWriter.println(identity.outputMetaData());
        entityWriter.println();
        entityWriter.println("Initial RefID\tCoDoSA Identity");
        
        for (Iterator<String> it = entityMap.getData().keySet().iterator(); it.hasNext();) {
            String key = it.next();
            ClusterRecord value = entityMap.getCluster(key);
            entityWriter.println(key + "\t" + value);
        }
    }
    
    public synchronized void outputChangeDetailReport(boolean detail, String path, String name) {
        int counter = 0;
        
        changeReportWriter.println("OYSTER Identity Change Report");
        changeReportWriter.println("Date          : " + now());
        changeReportWriter.println("RunScript Path: " + path);
        changeReportWriter.println("RunScript Name: " + name);
        changeReportWriter.println();

        changeReportWriter.println("Identity Change Summary Section");
        changeReportWriter.println("Count of Output Identities:	" + entityMap.getSize());
        changeReportWriter.println("Count of Input Identities:	" + numOfClusters);
        changeReportWriter.println("Count of Input Identities Updated and Written to Output:	" + updatedIdentities);
        changeReportWriter.println("Count of Input Identities Not Updated and Written to Output:	" + noChangedIdentities);
        changeReportWriter.println("Count of Input Identities Merged:	" + mergedIdentities);
        changeReportWriter.println("Count of New Identities Created:	" + newIdentities);
        changeReportWriter.println("Count of Error Identities:	" + errorIdentities);
        changeReportWriter.println();
        changeReportWriter.println();

        if (entityMap.getSize() != (numOfClusters - mergedIdentities + newIdentities)) {
            System.out.println("##ERROR: Output Identities != Input Identities - Merged Identities + New Identities");
        }
        if (numOfClusters != (updatedIdentities + noChangedIdentities)) {
            System.out.println("##ERROR: Input Identities != Input Identities Update + Input Identities Not Updated");
        }
        
        changeReportWriter.println("Identity Change Detail Section");
        changeReportWriter.println("New Identities Created");
        
        if (detail) {
        changeReportWriter.println("Identifier\tReferences");
        } else {
            changeReportWriter.println("Identifier");
        }
        
        for (Iterator<String> it = entityMap.getData().keySet().iterator(); it.hasNext();) {
            String key = it.next();
            ClusterRecord value = entityMap.getCluster(key);
            if (value.determineClusterState().equals("N")) {
                changeReportWriter.print(value.getOysterID());
                
                if (detail) {
                    changeReportWriter.println("\t" + value.getValuesByAttribute("@RefID"));
                } else {
                    changeReportWriter.println();
                }
                counter++;
            }
            
            if (counter > maxChangeReportExamples) {
                break;
            }
        }
        changeReportWriter.println();
        changeReportWriter.println();

        counter = 0;
        changeReportWriter.println("Input Identities Merged");
        
        if (detail) {
        changeReportWriter.println("Input Identifier\tOutput Identifier");
        } else {
            changeReportWriter.println("Input Identifier");
        }
        
        for (Iterator<String> it = entityMap.getData().keySet().iterator(); it.hasNext();) {
            String key = it.next();
            ClusterRecord value = entityMap.getCluster(key);
            if (value.determineClusterState().equals("M") || value.determineClusterState().equals("Z")) {
                for (Iterator<String> it2 = value.getMerges().keySet().iterator(); it2.hasNext();){
                    String oysterID = it2.next();
                    changeReportWriter.println(oysterID + "\t" + value.getOysterID());
                    
                    if (detail) {
                        String oldRefIDs = value.getMerges().get(oysterID);
                        String newRefIDs = value.getValuesByAttribute("@RefID").replaceAll(oldRefIDs, "");
                        newRefIDs = newRefIDs.replaceAll("||", "");
                        
                        if (newRefIDs.startsWith("|")) {
                            newRefIDs = newRefIDs.substring(1);
                        }
                        
                        if (newRefIDs.endsWith("|")) {
                            newRefIDs = newRefIDs.substring(0, newRefIDs.length()-1);
                        }
                        
                        changeReportWriter.println(oldRefIDs + "\t" + newRefIDs);
                    }
                    counter++;
                }
            }
            
            if (counter > maxChangeReportExamples) {
                break;
            }
        }
        changeReportWriter.println();
        changeReportWriter.println();

        counter = 0;
        changeReportWriter.println("Input Identities Updated");
        
        if (detail) {
            changeReportWriter.println("Identifier\tReferences before update\tReferences after update");
        } else {
            changeReportWriter.println("Identifier");
        }
        
        for (Iterator<String> it = entityMap.getData().keySet().iterator(); it.hasNext();) {
            String key = it.next();
            ClusterRecord value = entityMap.getCluster(key);
            if (value.determineClusterState().equals("U")) {
                changeReportWriter.print(value.getOysterID());
                
                if (detail) {
                    String before = "", after = "";
                    for (int i = 0; i < value.getSize(); i++){
                        OysterIdentityRecord oir = value.getOysterIdentityRecord(i);
                        
                        if (oir.isInput()) {
                            before += oir.get("@RefID") + "|";
                        } else {
                            after += oir.get("@RefID") + "|";
                        }
                    }
                    if (before.endsWith("|")) {
                        before = before.substring(0, before.length()-1);
                    }
                    if (after.endsWith("|")) {
                        after = after.substring(0, after.length()-1);
                    }
                    changeReportWriter.print("\t" + before + "\t" + before + "|" + after);
                }
                changeReportWriter.println();
                counter++;
            }
            
            if (counter > maxChangeReportExamples) {
                break;
            }
        }
    }
    
    public synchronized void outputMergeMap() {
        mergeMapWriter.println("Input Identifier,Output Identifier");
        for (Iterator<String> it = entityMap.getData().keySet().iterator(); it.hasNext();) {
            String key = it.next();
            ClusterRecord value = entityMap.getCluster(key);
            if (value.determineClusterState().equals("M") || value.determineClusterState().equals("Z")) {
                for (Iterator<String> it2 = value.getMerges().keySet().iterator(); it2.hasNext();){
                    String oysterID = it2.next();
                    mergeMapWriter.println(oysterID + "," + value.getOysterID());
                }
            }
        }
    }

    private ClusterRecord cartesianProduct(ClusterRecord clusterRecord) {
        ClusterRecord cr = null;

        if (clusterRecord != null) {
            cr = clusterRecord.clone();

            if (clusterRecord.getSize() > 1) {
                for (int i = 0; i < clusterRecord.getSize(); i++) {
                    OysterIdentityRecord oir1 = clusterRecord.getOysterIdentityRecord(i);

                    for (int j = 0; j < clusterRecord.getSize(); j++) {
                        OysterIdentityRecord oir2 = clusterRecord.getOysterIdentityRecord(j);

                        // merge each record
                        if (i != j) {
                            // get a set of sets
                            Map<String, Set<String>> m = getSets(oir1, oir2);
//                            System.out.println(m);
                            
                            // now preform A × B
                            Map<String, String> metadata = oir1.getMetaData();
                            Iterator<Entry<String, String>> it = metadata.entrySet().iterator();
                            Entry<String, String> entry = it.next();
                            Set a = m.get(entry.getValue());
                            Set s;
//                            System.out.println(a);
                            do {
                                entry = it.next();
                                Set b = m.get(entry.getValue());
                                
                                s = new LinkedHashSet();
                                for (Iterator<String> itA = a.iterator(); itA.hasNext();) {
                                    String token = itA.next();
                                    for (Iterator<String> itB = b.iterator(); itB.hasNext();) {
                                        s.add(token + "|" + itB.next());
                                    }
                                }
                                a = s;
//                                System.out.println(a);
                            } while(it.hasNext());
                            
                            // now create an OysterIdentityRecord for each set 
                            // and insert into the ClusterRecord
                            for (Iterator<String> itS = a.iterator(); itS.hasNext();) {
                                String record = itS.next();
                                String [] token = record.split("[|]");
                                
                                OysterIdentityRecord oir = new OysterIdentityRecordMap();
                                for (int x = 0; x < token.length; x++) {
                                    String [] temp = token[x].split("[=]");
                                    oir.add(temp[0], temp[1]);
                                }
//                                System.out.println(oir);
                                cr.insertRecord(oir, true);
                            }
                        } else {
                            cr.insertRecord(oir1, true);
                        }
                    }
                }
//                System.out.println();
            }
        }

        return cr;
    }

    private Map<String, Set<String>> getSets(OysterIdentityRecord oir1, OysterIdentityRecord oir2) {
        Map<String, Set<String>> m = new LinkedHashMap<String, Set<String>>();

        // tag = attribute
        Map<String, String> metadata = oir1.getMetaData();

//        System.out.println("oir1: " + oir1.toString());
//        System.out.println("oir2: " + oir2.toString());
        for (Iterator<Entry<String, String>> it = metadata.entrySet().iterator(); it.hasNext();) {
            Entry<String, String> entry = it.next();
            Set s = new LinkedHashSet();

            String token = oir1.get(entry.getValue());
            if (token != null && !token.isEmpty()) {
                s.add(entry.getValue() + "=" + token);
            }

            token = oir2.get(entry.getValue());
            if (token != null && !token.isEmpty()) {
                s.add(entry.getValue() + "=" + token);
            }
//            System.out.println(s);

            m.put(entry.getValue(), s);
        }

        return m;
    }
}