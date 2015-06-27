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

package edu.ualr.oyster.er;

import edu.ualr.oyster.ErrorFormatter;
import edu.ualr.oyster.OysterExplanationFormatter;
import edu.ualr.oyster.core.OysterKeywords;
import edu.ualr.oyster.data.ClusterRecord;
import edu.ualr.oyster.data.ClusterRecordSet;
import edu.ualr.oyster.data.OysterIdentityRecord;
import java.io.IOException;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * OysterAssertionEngine.java
 * 
 * This class determines if records match based on an assertion and not
 * on the actual data held within the record (with the exception of the 
 * Assertion keys). Assertion allow for you to bring records together that 
 * would not match by any other mechanism . Assert requires a priori knowledge
 * that the records belong together.
 * 
 * Created on Sep 21, 2011 5:02:55 PM
 * @author Eric D. Nelson
 */
public class OysterAssertionEngine extends OysterEngine {
    
    protected String assertionType = null;
    private Map<String,ClusterRecord> clusters;
    private Map<String,Set<String>> oysterIDs = null;
    private Map<String, Map<String, Set<String>>> splits;
    protected boolean badAssert = false;
    protected int assertCode = 0;
    
    /**
     * Creates a new instance of OysterAssertionEngine
     */
    public OysterAssertionEngine(String assertionType, int recordType){
        super();
        
        this.assertionType = assertionType;
        this.recordType = recordType;
        
        if (assertionType.equalsIgnoreCase(OysterKeywords.ASSERT_STR_TO_STR)){
            clusters = new LinkedHashMap<String,ClusterRecord>();
        } else if (assertionType.equalsIgnoreCase(OysterKeywords.ASSERT_SPLIT_STR)){
            clusters = new LinkedHashMap<String,ClusterRecord>();
            oysterIDs = new LinkedHashMap<String, Set<String>>();
            splits = new LinkedHashMap<String, Map<String, Set<String>>>();
        }
    }
    
    /**
     * Creates a new instance of OysterAssertionEngine
     * @param logFile
     * @param logLevel
     */
    public OysterAssertionEngine (String logFile, Level logLevel, String assertionType, int recordType) {
        super();
        
        this.assertionType = assertionType;
        this.recordType = recordType;
        
        if (assertionType.equalsIgnoreCase(OysterKeywords.ASSERT_STR_TO_STR)){
            clusters = new LinkedHashMap<String,ClusterRecord>();
        } else if (assertionType.equalsIgnoreCase(OysterKeywords.ASSERT_SPLIT_STR)){
            clusters = new LinkedHashMap<String,ClusterRecord>();
            oysterIDs = new LinkedHashMap<String, Set<String>>();
            splits = new LinkedHashMap<String, Map<String, Set<String>>>();
        }
        
        try {
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
        } catch (SecurityException ex) {
            Logger.getLogger(OysterAssertionEngine.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch (IOException ex) {
            Logger.getLogger(OysterAssertionEngine.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }

    /**
     * Creates a new instance of OysterAssertionEngine
     * @param log
     */
    public OysterAssertionEngine (Logger log, String assertionType, int recordType) {
        super();
        
        this.assertionType = assertionType;
        this.recordType = recordType;
        
        if (assertionType.equalsIgnoreCase(OysterKeywords.ASSERT_STR_TO_STR)){
            clusters = new LinkedHashMap<String,ClusterRecord>();
        } else if (assertionType.equalsIgnoreCase(OysterKeywords.ASSERT_SPLIT_STR)){
            clusters = new LinkedHashMap<String,ClusterRecord>();
            oysterIDs = new LinkedHashMap<String, Set<String>>();
            splits = new LinkedHashMap<String, Map<String, Set<String>>>();
        }
        
        try {
            // initialize logger
            this.logger = log;
        } catch (SecurityException ex) {
            Logger.getLogger(OysterAssertionEngine.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }
    
    //==========================================================================
    //  ... Getter/Setters
    //==========================================================================
    /**
     * @return the badAssert
     */
    public boolean isBadAssert() {
        return badAssert;
    }

    /**
     * @return the assertCode
     */
    public int getAssertCode() {
        return assertCode;
    }
    
    //==========================================================================
    //  ... Assertion Methods
    //==========================================================================
    /**
     * Reference to Reference Assertion allows for references that would not
     * normally match based on any given rule set.
     * @param recordCount the current record count
     */
    public void assertRefToRef(long recordCount) {
        boolean asserted = false;
        String rule = "", index = "";
        ClusterRecord cr;
        
        if (logger.isLoggable(Level.INFO)) {
            StringBuilder sb = new StringBuilder(250);
            sb.append(System.getProperty("line.separator"))
              .append("Input: ");
            sb.append(clusterRecord.getMergedRecord());
            logger.info(sb.toString());
        }
        
        // Ask IdentityRepository for a list of assertion candidates
        Map<String, ClusterRecord> list = repository.getAssertionList(clusterRecord, assertionType);
        
        if (logger.isLoggable(Level.FINE)) {
            StringBuilder sb = new StringBuilder(250);
            sb.append("\tAssertion List:");
            for (Iterator<Entry<String, ClusterRecord>> it = list.entrySet().iterator(); it.hasNext();){
                Entry<String, ClusterRecord> entry = it.next();
                sb.append(System.getProperty("line.separator"))
                  .append("\t\t")
                  .append(entry.getKey());
                sb.append("=")
                  .append(entry.getValue().getMergedRecord().toExplanationString());
            }
            logger.fine(sb.toString());
        }
        
        int identityCount = 1;
        for(Iterator<Entry<String, ClusterRecord>> it = list.entrySet().iterator(); it.hasNext();){
            Entry<String, ClusterRecord> entry = it.next();
            cr = entry.getValue();
            
            if (logger.isLoggable(Level.INFO)) {
                StringBuilder sb = new StringBuilder(250);
                sb.append("\tCompare Input ")
                  .append(recordCount);
                sb.append(" to Identity ")
                  .append(identityCount);
                sb.append(" ")
                  .append(cr.getMergedRecord().toExplanationString());
                logger.info(sb.toString());
            }
            
            if (applyAssertion(cr.getMergedRecord())) {
                asserted = true;
                rule = assertionType;
                index = cr.getMergedRecord().get("@RefID");
                
                if (logger.isLoggable(Level.FINE)) {
                    StringBuilder sb = new StringBuilder(250);
                    sb.append("\tMatched Assertion Type:")
                      .append(rule);
                    sb.append(System.getProperty("line.separator"));
                    logger.fine(sb.toString());
                }
            }
            
            if (asserted){
                break;
            }
            identityCount++;
        }
        
        // Ask IdentityRespository to update/create identity
        if (index != null){
            manageEntity(index, rule, asserted, recordCount);
        } else{
            System.out.println("Null index in Assertion List!!!");
            if (logger.isLoggable(Level.INFO)){
                logger.info("Null index in Assertion List!!!");
            }
        }
        
        // update the Assertion IDs for any future candidates
        String assertKey = clusterRecord.getMergedRecord().get(assertionType);
        LinkedHashSet<String> s = repository.getAssertMap().get(assertKey);
        if (s == null) {
            s = new LinkedHashSet<String>();
        }
            
        String RefIDs = clusterRecord.getMergedRecord().get("@RefID");
        String [] refID = RefIDs.split("[|]");
        s.addAll(Arrays.asList(refID));
        repository.getAssertMap().put(assertKey, s);
    }
    
    /**
     * Reference to Structure Assertion allows for references to be added to a
     * specific cluster.
     * @param recordCount the current record count
     */
    public void assertRefToStr(long recordCount) {
        String rule = "", index = clusterRecord.getMergedRecord().get("@RefID");
        ClusterRecord cr;

        if (logger.isLoggable(Level.INFO)) {
            StringBuilder sb = new StringBuilder(250);
            sb.append(System.getProperty("line.separator"))
              .append("Input: ");
            sb.append(clusterRecord.getMergedRecord());
            logger.info(sb.toString());
        }

        // Ask IdentityRepository for a list of assertion candidates
        cr = repository.getEntityMap().getCluster(clusterRecord.getMergedRecord().get("@AssertRefToStr"));

        if (logger.isLoggable(Level.FINE)) {
            StringBuilder sb = new StringBuilder(250);
            sb.append("\tAssertion List:\t\t")
              .append(clusterRecord.getOysterID());
            sb.append("=")
              .append(cr.getMergedRecord().toExplanationString());
            sb.append(System.getProperty("line.separator"));
            logger.fine(sb.toString());
        }

        if (cr != null) {
            int identityCount = 1;

            if (logger.isLoggable(Level.INFO)) {
                StringBuilder sb = new StringBuilder(250);
                sb.append("\tCompare Input ")
                  .append(recordCount);
                sb.append(" to Identity ")
                  .append(identityCount);
                sb.append(" ")
                  .append(cr.getMergedRecord().toExplanationString());
                logger.info(sb.toString());
            }

            if (applyAssertion(cr.getMergedRecord())) {
                rule = assertionType;

                if (logger.isLoggable(Level.FINE)) {
                    StringBuilder sb = new StringBuilder(250);
                    sb.append("\tMatched Assertion Type:")
                      .append(rule);
                    sb.append(System.getProperty("line.separator"));
                    logger.fine(sb.toString());
                }
            }

            identityCount++;

            // Ask IdentityRespository to update/create identity
            manageEntity(cr, index, rule, recordCount);

            // update the Assertion IDs for any future candidates
            String assertKey = clusterRecord.getMergedRecord().get(assertionType);
            LinkedHashSet<String> s = repository.getAssertMap().get(assertKey);
            if (s == null) {
                s = new LinkedHashSet<String>();
            }
            String RefIDs = clusterRecord.getMergedRecord().get("@RefID");
            String[] refID = RefIDs.split("[|]");
            s.addAll(Arrays.asList(refID));
            repository.getAssertMap().put(assertKey, s);
        } else {
            System.out.println("Null Assertion List for OID " + clusterRecord.getOysterID());
            if (logger.isLoggable(Level.INFO)) {
                StringBuilder sb = new StringBuilder(250);
                sb.append("Null Assertion List for OID ")
                  .append(clusterRecord.getOysterID());
                logger.info(sb.toString());
            }
        }
    }
    
    /**
     * Structure to Structure Assertion allows for clusters to be merged together.
     * @param recordCount the current record count
     */
    public void assertStrToStr(long recordCount){
        ClusterRecord cr;
        String assertKey = clusterRecord.getMergedRecord().get(assertionType);
        LinkedHashSet<String> s = repository.getAssertMap().get(assertKey);
        if (s == null) {
            s = new LinkedHashSet<String>();
        }
            
        String refID = clusterRecord.getMergedRecord().get("@RefID");
        s.add(refID);
        repository.getAssertMap().put(assertKey, s);
        
        cr = clusterRecord.clone();
        cr.setOysterID(cr.getOysterIdentityRecord(0).get("@OID"));
        clusters.put(refID, cr);
    }
    
    /**
     * Split Structure Assertion breaks up a specific cluster into multiple 
     * clusters and tags the clusters with negative information to restrict
     * then from being brought back together due to subsequent runs.
     * @param recordCount the current record count
     */
    public void assertSplitStr(long recordCount) {
        ClusterRecord cr;
        String assertKey = clusterRecord.getMergedRecord().get(assertionType);
        Map<String, Set<String>> m = splits.get(assertKey);

        if (m == null) {
            m = new LinkedHashMap<String, Set<String>>();
        }

        String oid = clusterRecord.getMergedRecord().get(OysterKeywords.OID);
        Set<String> s = m.get(oid);

        if (s == null) {
            s = new LinkedHashSet<String>();
        }

        String rid = clusterRecord.getMergedRecord().get(OysterKeywords.RID);
        s.add(rid);

        m.put(oid, s);
        splits.put(assertKey, m);

        LinkedHashSet<String> s1 = repository.getAssertMap().get(assertKey);
        if (s1 == null) {
            s1 = new LinkedHashSet<String>();
        }

        String refID = clusterRecord.getMergedRecord().get("@RefID");
        s1.add(refID);
        repository.getAssertMap().put(assertKey, s1);

        // get the OIR from the cluster and make a new Cluster record of just this OIR
        cr = repository.getEntityMap().getCluster(clusterRecord.getOysterIdentityRecord(0).get("@OID"));
        if (cr != null) {
            for (int i = 0; i < cr.getSize(); i++) {
                OysterIdentityRecord oir = cr.getOysterIdentityRecord(i);

                if (oir.get("@RefID").equalsIgnoreCase(clusterRecord.getOysterIdentityRecord(0).get("@RID"))) {
                    // add Extra split data to OIR
                    oir.add("@RID", clusterRecord.getOysterIdentityRecord(0).get("@RID"));
                    oir.add("@OID", clusterRecord.getOysterIdentityRecord(0).get("@OID"));
                    oir.add("@AssertSplitStr", clusterRecord.getOysterIdentityRecord(0).get("@AssertSplitStr"));

                    cr = new ClusterRecordSet(recordType);
                    cr.insertRecord(oir);
                    cr.setOysterID(repository.getNextID(cr.getMergedRecord(), false));
                    break;
                }
            }
            clusters.put(refID, cr);
        } else {
            StringBuilder sb = new StringBuilder(100);
            sb.append("##WARNING: Assertion @OID ")
                    .append(clusterRecord.getOysterIdentityRecord(0).get("@OID"))
                    .append(" not found in Identity File.")
                    .append(System.getProperty("line.separator"));
            logger.severe(sb.toString());
            System.out.println(sb.toString());
            badAssert = true;
            assertCode = -3000;
        }
    }
    
    /**
     * This method is used to handle assertions. By default the values must be
     * equal (case insensitive).
     * @param oir the OysterIdentityRecord to match to the current record
     * @param relative true if this is a relative assertion, otherwise false
     * @return true if a match, otherwise false
     */
    private boolean applyAssertion(OysterIdentityRecord oir) {
        boolean flag = false;
        String assert1 = null, assert2 = null;
        
        if (assertionType.equalsIgnoreCase(OysterKeywords.ASSERT_REF_TO_REF)){
            assert1 = oir.get(assertionType);
            assert2 = clusterRecord.getMergedRecord().get(assertionType);
        } else if (assertionType.equalsIgnoreCase(OysterKeywords.ASSERT_REF_TO_STR)){
            assert1 = oir.get("@AssertRefToStr");
            assert2 = clusterRecord.getMergedRecord().get(assertionType);
        }
        
        if (assert1 != null && assert2 != null && 
                assert1.equalsIgnoreCase(assert2)){
            flag = true;
        }
        
        return flag;
    }
    
    /**
     * Preform the assertion on this group of records
     * @param recordCount the current record count
     */
    public void postAssertStrToStr(long recordCount){
        // determine the minimum Cluster
        String oysterID = "", minRefID;
        ClusterRecord cr1;
        
        for (Iterator<String> it = repository.getAssertMap().keySet().iterator(); it.hasNext();) {
            String index = it.next();
            LinkedHashSet<String> s = repository.getAssertMap().get(index);

            Iterator<String> it2 = s.iterator();
            String refID2, refID1 = it2.next();
            cr1 = clusters.get(refID1);
            
            // determine the minimum oysterID
            if (s.size() > 1) {
                do {
                    refID2 = it2.next();
                    ClusterRecord cr2 = clusters.get(refID2);

                    oysterID = repository.getMinOysterID(cr1, cr2);
                    // save the min refID that belongs with the min OysterID
                    if (cr1.getOysterID().equals(oysterID)){
                        minRefID = refID1;
                    } else {
                        minRefID = refID2;
                    }
                    cr1 = clusters.get(minRefID);
                } while (it2.hasNext());
            } else {
                oysterID = cr1.getOysterID();
            }
        
            // Merge all clusters in to the minimum cluster
            cr1 = repository.getEntityMap().getCluster(oysterID);
            for (it2 = s.iterator(); it2.hasNext();) {
                    String refID = it2.next();

                    String oid = clusters.get(refID).getOysterID();

                    if (!cr1.getOysterID().equals(oid)) {
                        ClusterRecord cr2 = repository.getEntityMap().getCluster(oid);
                        repository.getEntityMap().removeCluster(oid);
                        
                        Set<String> set = new LinkedHashSet<String>();
                        set.add(assertionType);
                        cr1.merge(cr2, repository.getMid(), set, repository.isTraceOn());
                        cr1.getStrToStr().add(oid);
                        
                        repository.setMergedIdentities(repository.getMergedIdentities() + 1);
                    }
                }

//            cr1.setClusterType("Z");
            repository.setUpdatedIdentities(repository.getUpdatedIdentities() + 1);
            repository.updateIdentity(oysterID, cr1);
        } 
    }
    
    public void postAssertNegStr(long recordCount) {
        // determine the minimum Cluster
        String oysterID = "", minRefID = "";
        ClusterRecord cr1;

        // validate that not all records are being removed from a cluster
        if (checkNegClusters()) {
            // validate that the RID and OID belong together
            if (validateOidRidCombo()) {
                // now preform the split
                for (Iterator<String> it = repository.getAssertMap().keySet().iterator(); it.hasNext();) {
                    String index = it.next();
                    LinkedHashSet<String> s = repository.getAssertMap().get(index);

                    Iterator<String> it2 = s.iterator();
                    String refID2, refID1 = it2.next();
                    cr1 = clusters.get(refID1);

                    // determine the minimum oysterID
                    if (s.size() > 1) {
                        do {
                            refID2 = it2.next();
                            ClusterRecord cr2 = clusters.get(refID2);

                            oysterID = repository.getMinOysterID(cr1, cr2);
                            // save the min refID that belongs with the min OysterID
                            if (cr1.getOysterID().equals(oysterID)) {
                                minRefID = refID1;
                            } else {
                                minRefID = refID2;
                            }
                            cr1 = clusters.get(minRefID);
                        } while (it2.hasNext());
                    } else {
                        minRefID = refID1;
                        oysterID = cr1.getOysterID();
                    }

                    // get the min cluster
                    cr1 = clusters.get(minRefID);

                    // remove from Master Cluster
                    for (Iterator<String> it3 = s.iterator(); it3.hasNext();) {
                        String refID = it3.next();
                        ClusterRecord cr = clusters.get(refID);
//                        System.out.println("cr: " + cr);

                        ClusterRecord crMaster = repository.getEntityMap().getCluster(cr.getOysterIdentityRecord(0).get("@OID"));
                        if (crMaster != null) {
//                        System.out.println("crMaster: " + crMaster);

                            for (int i = 0; i < crMaster.getSize(); i++) {
                                OysterIdentityRecord oir = crMaster.getOysterIdentityRecord(i);

                                if (oir.get("@RefID").equalsIgnoreCase(cr.getOysterIdentityRecord(0).get("@RID"))) {
                                    crMaster.remove(i);

                                    crMaster.getNegStrToStr().add(oysterID);
                                    cr.getNegStrToStr().add(crMaster.getOysterID());

                                    Set<String> s1 = oysterIDs.get(crMaster.getOysterID());

                                    if (s1 == null) {
                                        s1 = new LinkedHashSet<String>();
                                    }

                                    s1.add(oysterID);
                                    oysterIDs.put(crMaster.getOysterID(), s1);

                                    repository.getEntityMap().add(crMaster);
                                    break;
                                }
                            }
                        }
//                    System.out.println();
//                    System.out.println();
//                    crMaster.setClusterType("U");
                    }

                    // merge all sub Clusters
                    for (Iterator<String> it3 = s.iterator(); it3.hasNext();) {
                        String refID = it3.next();
                        ClusterRecord cr = clusters.get(refID);

                        String oid = cr.getOysterID();

                        if (!cr1.getOysterID().equals(oid)) {
                            Set<String> set = new LinkedHashSet<String>();
                            set.add(assertionType);
                            cr1.merge(cr, repository.getMid(), set, repository.isTraceOn());
                        }
                    }

                    // update
                    repository.updateIdentity(oysterID, cr1);
                }
            }
        }
    }

    /**
     * This method validates that at least one reference is left in the original 
     * Cluster after the split. If all the records are removed then the bad 
     * assertion flag is set.
     * @return true if at least one record is in every cluster after the check,
     * otherwise false;
     */
    private boolean checkNegClusters() {
        boolean flag = true;
        Map<String, Set<String>> check = new LinkedHashMap<String, Set<String>>();

        // get the ref id for each oid across assertion groups.
        for (Iterator<String> it = splits.keySet().iterator(); it.hasNext();) {
            String assertKey = it.next();

            Map<String, Set<String>> m = splits.get(assertKey);

            for (Iterator<String> it2 = m.keySet().iterator(); it2.hasNext();) {
                String oid = it2.next();
                Set<String> s1 = m.get(oid);
                Set<String> s2 = check.get(oid);

                if (s2 == null) {
                    s2 = new LinkedHashSet<String>();
                }

                s2.addAll(s1);
                check.put(oid, s2);
            }
        }

        // now check to see if the number of assertions per OID is less than 
        // the total references in the cluster
        for (Iterator<String> it = check.keySet().iterator(); it.hasNext();) {
            String oid = it.next();
            Set<String> s = check.get(oid);

            ClusterRecord cr = repository.getEntityMap().getCluster(oid);

            if (s.size() >= cr.getSize()) {
                StringBuilder sb = new StringBuilder(100);
                sb.append("##ERROR: Assertion @OID ")
                        .append(oid)
                        .append(" will remove all references from the existing Cluster.")
                        .append(System.getProperty("line.separator"));
                logger.severe(sb.toString());
                System.out.println(sb.toString());
                badAssert = true;
                assertCode = -3100;
                flag = false;
                break;
            }
        }
        return flag;
    }

    /**
     * This method validates that each OID/RID combination actually exists in 
     * the repository.
     * @return true if every OID/RID combo exists, otherwise false
     */
    private boolean validateOidRidCombo() {
        boolean flag = true;
        
        for (Iterator<String> it = splits.keySet().iterator(); it.hasNext();) {
            String assertKey = it.next();
            
            Map<String, Set<String>> m = splits.get(assertKey);
            for (Iterator<String> it2 = m.keySet().iterator(); it2.hasNext();) {
                String oid = it2.next();
                Set<String> s = m.get(oid);
                
                ClusterRecord cr = repository.getEntityMap().getCluster(oid);
                Set<String> s2 = cr.getField(OysterKeywords.REFID);
                
                if (!s2.containsAll(s)) {
                    StringBuilder sb = new StringBuilder(100);
                    sb.append("##ERROR: Assertion @OID ")
                            .append(oid)
                            .append(" is not found with one or more of the following @RID's ")
                            .append(s)
                            .append(System.getProperty("line.separator"));
                    logger.severe(sb.toString());
                    System.out.println(sb.toString());
                    badAssert = true;
                    assertCode = -3200;
                    flag = false;
                    break;
                }
            }
            
            if (!flag){
                break;
            }
        }
        
        return flag;
    }
    
    public void postNeg(){
        for (Iterator<String> it = oysterIDs.keySet().iterator(); it.hasNext();) {
            String oysterID = it.next();
            Set<String> s = oysterIDs.get(oysterID);
            
            for (Iterator<String> it2 = s.iterator(); it2.hasNext();) {
                String subOysterID = it2.next();
                ClusterRecord cr = repository.getEntityMap().getData().get(subOysterID);
                
                cr.getNegStrToStr().addAll(s);
                cr.getNegStrToStr().remove(subOysterID);
            }
        }
    }
    
    /**
     * This method is used with the AssertRefToRef and determines the status of 
     * the input record then updates the Entity Map, Entity Set, Link amp and 
     * Value Index.
     * @param cr the matched ClusterRecord (can be null is not matched)
     * @param index the RefID number that was matched  (can be empty is not matched)
     * @param rule the rule that was matched on (can be empty is not matched)
     * @param match whether the input record matched a candidate record or not
     * @param recordCount the current record count
     */
    private void manageEntity(String index, String rule, boolean match, long recordCount) {
        ClusterRecord cr;
        
        // if the index is empty or match flag is false then this is a new 
        // record that matches nothing
        if (index.equals("") || !match) {
            String id = clusterRecord.getOysterID();
            if (id == null || id.trim().equals("")) {
                id = repository.getNextID(clusterRecord.getMergedRecord(), false);
                clusterRecord.setOysterID(id);

                cr = clusterRecord.clone();
                repository.addNewIdentity(id, cr);
            } else {
                cr = clusterRecord.clone();
                repository.updateIdentity(id, cr);
            }

            repository.addIndex(cr, false);
            repository.addLink(cr.getMergedRecord(), id, rule);

            if (logger.isLoggable(Level.INFO)) {
                StringBuilder sb = new StringBuilder(250);
                sb.append("\tNew Entity ")
                  .append(cr.getMergedRecord().toExplanationString())
                  .append(System.getProperty("line.separator"));
                sb.append("\tNew Index: ")
                  .append(cr.getMergedRecord())
                  .append(System.getProperty("line.separator"));
                sb.append("\tNew LinkMap{")
                  .append(cr.getMergedRecord().get("@RefID"));
                sb.append("}, ")
                  .append(cr.getMergedRecord().toExplanationString())
                  .append(System.getProperty("line.separator"));
                logger.info(sb.toString());
            }
        } else if (match) {
            if (logger.isLoggable(Level.INFO)) {
                StringBuilder sb = new StringBuilder(100);
                sb.append(System.getProperty("line.separator"))
                  .append("\tSatisfies Assertion Type: ")
                  .append(rule);
                logger.info(sb.toString());
            }

            String oysterID = null;
            String [] refID = index.split("[|]");
            for (int i = 0; i < refID.length; i++) {
                oysterID = repository.getLinkMap().get(refID[i]);

            if (oysterID == null) {
                    oysterID = repository.getRefIDLookup().get(refID[i]);
                }
                
                if (oysterID != null) {
                    index = refID[i];
                    break;
                }
            }
            cr = repository.getEntityMap().getCluster(oysterID);
            repository.getEntityMap().removeCluster(oysterID);

            // deterimine persistance of the OysterID
            ClusterRecord minCR;
            Set<String> set = new LinkedHashSet<String>();
            set.add(assertionType);
            
            String minOysterID = repository.getMinOysterID(clusterRecord, cr);
            if (minOysterID.equalsIgnoreCase(clusterRecord.getOysterID())){
                minCR = clusterRecord.clone();
                minCR.merge(cr, repository.getMid(), set, repository.isTraceOn());
            } else {
                minCR = cr.clone();
                minCR.merge(clusterRecord, repository.getMid(), set, repository.isTraceOn());
            }
            minCR.setOysterID(minOysterID);
            
            repository.updateIdentity(minOysterID, minCR);
            repository.addIndex(minCR, false);
            // update Link Map
            Set<String> s = minCR.getField("@RefID");
            for (Iterator<String> it = s.iterator(); it.hasNext();) {
                repository.updateLink(it.next(), minOysterID, rule, index);
            }
            
            if (logger.isLoggable(Level.INFO)) {
                StringBuilder sb = new StringBuilder(250);
                sb.append("\tAssign Entity ")
                  .append(index)
                  .append(" to Input ")
                  .append(recordCount);
                sb.append(System.getProperty("line.separator"));

                if (cr != null) {
                    sb.append("\tUpdate Entity: ")
                      .append(cr.getMergedRecord().toExplanationString());
                } else {
                    sb.append("\tUpdate Entity: ")
                      .append(clusterRecord.getMergedRecord().toExplanationString());
                }
                sb.append(System.getProperty("line.separator"));
                logger.info(sb.toString());
            }

            if (logger.isLoggable(Level.INFO)) {
                StringBuilder sb = new StringBuilder(250);
                sb.append("\tUpdate Index: ").append(index).append(" for ri ").append(clusterRecord.getMergedRecord());
                logger.fine(sb.toString());
            }
        }
    }
    
    /**
     * This method is used for the AssertRefToStr and determines the status of 
     * the input record then updates the Entity Map, Entity Set, Link map and 
     * Value Index.
     * @param cr the matched ClusterRecord (can be null is not matched)
     * @param index the RefID number that was matched  (can be empty is not matched)
     * @param rule the rule that was matched on (can be empty is not matched)
     * @param recordCount the current record count
     */
    private void manageEntity(ClusterRecord cr, String index, String rule, long recordCount){
        if (logger.isLoggable(Level.INFO)) {
            StringBuilder sb = new StringBuilder(100);
            sb.append(System.getProperty("line.separator"))
              .append("\tSatisfies Assertion Type: ")
              .append(rule);
            logger.info(sb.toString());
        }

        // remove any assertions
//        clusterRecord.getOysterIdentityRecord(0).remove(assertionType);
        Set<String> set = new LinkedHashSet<String>();
        set.add(assertionType);
        cr.merge(clusterRecord, repository.getMid(), set, repository.isTraceOn());
//        cr.setClusterType("N, X");
        repository.updateIdentity(cr.getOysterID(), cr);
        repository.addIndex(cr, false);

        // update Link Map
        Set<String> s = cr.getField("@RefID");
        for (Iterator<String> it = s.iterator(); it.hasNext();) {
            String refID = it.next();
            repository.updateLink(refID, cr.getOysterID(), rule, index);
        }

        if (logger.isLoggable(Level.INFO)) {
            StringBuilder sb = new StringBuilder(250);
            sb.append("\tAssign Entity ")
              .append(index)
              .append(" to Input ")
              .append(recordCount);
            sb.append(System.getProperty("line.separator"));

            if (cr != null) {
                sb.append("\tUpdate Entity: ")
                  .append(cr.getMergedRecord().toExplanationString());
            } else {
                sb.append("\tUpdate Entity: ")
                  .append(clusterRecord.getMergedRecord().toExplanationString());
            }
            sb.append(System.getProperty("line.separator"));
            logger.info(sb.toString());
        }

        if (logger.isLoggable(Level.INFO)) {
            StringBuilder sb = new StringBuilder(250);
            sb.append("\tUpdate Index: ").append(index).append(" for ri ").append(clusterRecord.getMergedRecord());
            logger.fine(sb.toString());
        }
    }
}
