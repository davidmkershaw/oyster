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
import edu.ualr.oyster.association.matching.OysterComparator;
import edu.ualr.oyster.data.ClusterRecord;
import edu.ualr.oyster.data.OysterIdentityRecord;
import edu.ualr.oyster.optimization.Matrix;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Implements resolution rules in reference source to determine if reference is 
 * new entity or same as an existing entity. This Engine uses the Fellegi Sunter
 * Clustering methodology.
 * 
 * Responsibilities:
 * <ul>
 * <li>Apply resolution rules from reference source</li>
 * <li>Resolve reference</li>
 * </ul>
 * @author Eric D. Nelson
 */
public class OysterClusterEngine extends OysterResolutionEngine {
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.C3246F28-9E8A-B49F-B148-25190DA862CA]
    // </editor-fold> 
    /**
     * Creates a new instance of OysterClusterEngine
     * @param logFile
     * @param logLevel
     */
    public OysterClusterEngine (String logFile, Level logLevel, int recordType) {
        super(logFile, logLevel, recordType);
        mergedList = false;
        postConsolidation = false;
    }

    /**
     * Creates a new instance of OysterClusterEngine
     * @param log
     */
    public OysterClusterEngine (Logger log, int recordType) {
        super(log, recordType);
        mergedList = false;
        postConsolidation = false;
    }
    
    /**
     * Creates a new instance of OysterClusterEngine
     */
    public OysterClusterEngine (int recordType) {
        super(recordType);
        mergedList = false;
        postConsolidation = false;
    }
    
    /**
     * This is the heart of the default <code>OysterClusterEngine</code>. The
     * engine takes the current reference items pulls a candidate list of possibles
     * from the <code>OysterIdentityRepository</code>. The reference items are
     * compared against the candidate list one at a time to determine if a match
     * is produced. 
     * 
     * Two mechanism are used to control the performance and quality of the match.
     * First, an index is used to produce candidates. These candidates can be 
     * returned in a random or descending frequency sorted order. In the sorted
     * order, the records at the top of the list have the greatest chance of 
     * matching because it contains more elements that matched to the index.
     * The second mechanism, is the filter. The filter is a list of minimum number
     * elements that must exist for a rule to pass. This is used to boost performance
     * it removes rules from the candidate list that would have never passed before
     * any complex calculations are performed.
     * 
     * Currently, ALL candidates that pass the filter are evaluated UNLESS they have
     * been consolidated in a previous iteration of during this specific call.
     * @param sort true if a sorted candidate list is to be used otherwise false.
     * @param recordCount the current record count
     */
    @Override
    public void integrateSource (boolean sort, long recordCount) {
        boolean matched = false, overallMatch = false;
        int matchedCount = 0;
        ClusterRecord cr = null;
        long start = System.currentTimeMillis(), stop;
        
        if (logger.isLoggable(Level.INFO)) {
            StringBuilder sb = new StringBuilder(100);
            sb.append(System.getProperty("line.separator"))
              .append("Input: ").append(clusterRecord.getMergedRecord());
            logger.info(sb.toString());
        }        
/*
        if (clusterRecord.getMergedRecord().get("@RefID").equals("Test17e.2020")){
            System.out.println();
        }
*/
        // Ask IdentityRepository for a list of candidates
        Map<String, ClusterRecord> list;
        if ((list = repository.getCandidateList(clusterRecord, sort, primaryFilter, lcrdMinSize, isByPassFilter(), mergedList)).isEmpty()){
            if (secondaryFilter != null) {
                list = repository.getCandidateList(clusterRecord, sort, secondaryFilter, lcrdMinSize, isByPassFilter(), mergedList);
            }
        }
        
        int unfiltered = list.size();
        totalCandidatesSize += list.size();
        
        // Remove duplicate Clusters
        list = removeDuplicateClusters(list);
        
        int filtered = list.size();
        totalCandidatesDeDupSize += list.size();
        if (list.size() > 0) {
            totalCandidates++;
        }
        
        if (logger.isLoggable(Level.FINE)) {
            logger.fine("\tCandidate List:");
            for (Iterator<Entry<String, ClusterRecord>> it = list.entrySet().iterator(); it.hasNext();){
                Entry<String, ClusterRecord> entry = it.next();
                cr = entry.getValue();
                for (int i = 0; i < cr.getSize(); i++) {
                    OysterIdentityRecord oir = cr.getOysterIdentityRecord(i);
                    StringBuilder sb = new StringBuilder(100);
                    sb.append("\t\t").append(entry.getKey()).append("=").append(oir.toExplanationString());
                    logger.fine(sb.toString());
                }
            }
            logger.fine("");
        }
/*
            if (unfiltered > 100) {
                StringBuilder sb = new StringBuilder(100);
                sb.append("Input: ").append(clusterRecord.getMergedRecord());
                logger.severe(sb.toString());
                sb = new StringBuilder(100);
                sb.append("Unfilter: ").append(unfiltered).append("\tFilter: ").append(filtered);
                logger.fine(sb.toString());
            }
        }
*/
        String index, overallIndex = "", rule = "";
        Map<String, String> consolidate = new LinkedHashMap<String, String>();
        ArrayList<String> prevRefIDs = new ArrayList<String>();
        int identityCount = 1;
        for (Iterator<Entry<String, ClusterRecord>> it = list.entrySet().iterator(); it.hasNext();) {
            Entry<String, ClusterRecord> entry = it.next();
            index = entry.getKey();
            cr = entry.getValue();

            matched = false;
            for (int i = 0; i < cr.getSize(); i++) {
                OysterIdentityRecord oir = cr.getOysterIdentityRecord(i);
                if (logger.isLoggable(Level.INFO)) {
                    StringBuilder sb = new StringBuilder(100);
                    sb.append("\tCompare Input ").append(recordCount).append(" to Identity ").append(identityCount).append(" ").append(oir.toExplanationString());
                    logger.info(sb.toString());
                }
                /*
                 if (oir == null){
                 System.err.println(cr.toString());
                 }
                 */
                Set<String> completeRules = new TreeSet<String>();
                if (!matched && !prevRefIDs.contains(oir.get("@RefID")) && applyRules(oir)) {
                    if (logger.isLoggable(Level.FINE)) {
                        logger.fine("matrix");
                        logger.fine(matrix.toString());
                        logger.fine("");
                        logger.fine("masks");
                    }

                    // does the matrix match any of the masks
                    for (Iterator<String> it2 = masks.keySet().iterator(); it2.hasNext();) {
                        String key = it2.next();
                        Matrix m = masks.get(key);

                        if (logger.isLoggable(Level.FINE)) {
                            logger.fine(m.toString());
                        }

                        // create temp rule with the AND Operator
                        Matrix temp = null;
                        try {
                            temp = (Matrix) m.clone();
                            temp.fill(false);

                            for (int row = 0; row < m.getRows().size(); row++) {
                                for (int col = 0; col < m.getColumns().size(); col++) {
                                    if (m.getMatrix()[row][col] && matrix.getMatrix()[row][col]) {
                                        temp.getMatrix()[row][col] = true;
                                    }
                                }
                            }
                        } catch (CloneNotSupportedException ex) {
                            Logger.getLogger(OysterMergeEngine.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
                        }

                        // If the mask matches the temp rule then it's a match
                        if (m.equals(temp)) {
                            matched = overallMatch = true;
                            overallIndex = index;
                            completeRules.add(key);
                            rule = key;

                            long value = 0;
                            if (completeRuleFiring.containsKey(completeRules.toString())) {
                                value = completeRuleFiring.get(completeRules.toString());
                            }
                            value++;
                            completeRuleFiring.put(completeRules.toString(), value);

                            if (matchedCount == 0) {
                                rule = key;
                                value = 0;
                                if (ruleFreq.containsKey(key)) {
                                    value = ruleFreq.get(key);
                                }
                                value++;
                                ruleFreq.put(key, value);

                                if (logger.isLoggable(Level.FINE)) {
                                    StringBuilder sb = new StringBuilder(100);
                                    sb.append("\tMatched Rule:").append(key);
                                    logger.fine(sb.toString());
                                    logger.fine("");
                                }
                                totalMatchedCount++;
                            }
                            matchedCount++;
                        }
                    }
                    prevRefIDs.add(oir.get("@RefID"));
                }

                // save the current RefID
//            prevRefIDs.addElement(oir.get("@RefID"));

                // check to see if this result can be consildated with a previous result
                if (matched) {
                    consolidate.put(index, rule);
                    if (capture) {
                        matched = false;
                    }
                    break;
                }
            }

            // take the first match if in non-capture mode
            if (matched && !capture) {
                break;
            }

            identityCount++;
        }

        matched = overallMatch;
        index = overallIndex;

        stop = System.currentTimeMillis();

        // reset matched flag and get the matched index
        if (consolidate.size() > 0) {
            matched = true;
        }

        // Ask IdentityRespository to update/create identity
        if (index != null) {
            manageEntity(cr, index, rule, matched, recordCount, consolidate);
        } else {
            System.out.println("Null index in Candidate List!!!");
            if (logger.isLoggable(Level.INFO)) {
                logger.info("Null index in Candidate List!!!");
            }
        }

        if (matched && logger.isLoggable(Level.FINEST)) {
            dump();
        }

        // do the latency stats
        long latency = stop - start;
        if (matched) {
            matchingLatency += latency;
            maxMatchingLatency = Math.max(maxMatchingLatency, latency);
            minMatchingLatency = Math.min(minMatchingLatency, latency);
        } else {
            nonMatchingLatency += latency;
            maxNonMatchingLatency = Math.max(maxNonMatchingLatency, latency);
            minNonMatchingLatency = Math.min(minNonMatchingLatency, latency);
        }
    }

    /**
     * This method determines the status of the input record then updates the 
     * Entity Map, Entity Set, Link amp and Value Index.
     * @param cr the matched ClusterRecord (can be null is not matched)
     * @param index the RefID number that was matched  (can be empty is not matched)
     * @param rule the rule that was matched on (can be empty is not matched)
     * @param match whether the input record matched a candidate record or not
     * @param recordCount the current record count
     * @param consolidate a list of all the candidates that were found to match 
     * (can be empty is not matched)
     */
    private void manageEntity(ClusterRecord cr, String index, String rule, boolean match, long recordCount, Map<String, String> consolidate){
        // if the index is empty or match flag is false then this is a new 
        // record that matches nothing
        if (index.equals("") || !match) {
            if (capture) {
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

                repository.addIndex(cr, mergedList);
                repository.addLink(cr.getMergedRecord(), id, rule);
                    
                if (logger.isLoggable(Level.INFO)) {
                    StringBuilder sb = new StringBuilder(250);
                    sb.append("\tNew Entity ").append(cr.getOysterID())
                      .append(" ")
                      .append(cr.getMergedRecord().toExplanationString())
                      .append(System.getProperty("line.separator"));
                    sb.append("\tNew Index: ").append(cr.getMergedRecord())
                      .append(System.getProperty("line.separator"));
                    sb.append("\tNew LinkMap{")
                      .append(cr.getMergedRecord().get("@RefID"))
                      .append("}, ")
                      .append(cr.getMergedRecord().toExplanationString());
                    logger.info(sb.toString());
                }
            } else {
                /*                    
                String id = repository.getNextID(oir, true);
                repository.addLink(oir, id, rule);
                 */
                cr = clusterRecord.clone();
                
                repository.addLink(cr.getMergedRecord(), "XXXXXXXXXXXXXXXX", rule);

                if (logger.isLoggable(Level.INFO)) {
                    StringBuilder sb = new StringBuilder(100);
                    sb.append("\tNo Capture: LinkMap{")
                      .append(cr.getMergedRecord().get("@RefID"))
                      .append("}, ")
                      .append(cr.getMergedRecord().toExplanationString());
                    logger.info(sb.toString());
                }
            }
        } else if (match) {
            int min = Integer.MAX_VALUE;
            String minOysterID = "";
            ClusterRecord minCR;
//            minCR.merge(clusterRecord);
            
            // handle any negative assertion
            // first let's see if there is any negative info for the matching candidates
            Map<String, String> negative = new LinkedHashMap<String, String>();
            Map<String, String> negBookKeeping = new LinkedHashMap<String, String>();
            for (Iterator<Entry<String,String>> it = consolidate.entrySet().iterator(); it.hasNext();) {
                Entry<String,String> entry = it.next();
                String oysterID = repository.getLinkMap().get(entry.getKey());

                if (oysterID == null) {
                    oysterID = repository.getRefIDLookup().get(entry.getKey());
                }
                cr = repository.getEntityMap().getCluster(oysterID);
                
                negBookKeeping.put(cr.getOysterID(), entry.getKey());
                for (Iterator<String> it2 = cr.getNegStrToStr().iterator(); it2.hasNext();) {
                    negative.put(it2.next(), cr.getOysterID());
                }
            }
            
            // now lets see what we can reject
            for (Iterator<Entry<String,String>> it = negative.entrySet().iterator(); it.hasNext();) {
                Entry<String,String> entry = it.next();
                if (negative.containsValue(entry.getKey())){
                    // remove cluster
                    String refID = negBookKeeping.get(entry.getValue());
                    consolidate.remove(refID);
                }
            }
            
            // now lets see if the remainder has a negative connection to the input record
            for (Iterator<String> it = this.clusterRecord.getNegStrToStr().iterator(); it.hasNext();) {
                String s = it.next();
                if (negative.containsValue(s)){
                    // remove cluster
                    
                }
            }
            
            // get the min Oyster ID
            if (consolidate.size() > 1){
                Object [] keys = consolidate.keySet().toArray();
                String refID = (String) keys[0];
                String oysterID = repository.getLinkMap().get(refID);

                if (oysterID == null) {
                    oysterID = repository.getRefIDLookup().get(refID);
                }
                cr = repository.getEntityMap().getCluster(oysterID);

                for (int i = 1; i < keys.length; i++) {
                    refID = (String) keys[i];
                    oysterID = repository.getLinkMap().get(refID);

                    if (oysterID == null) {
                        oysterID = repository.getRefIDLookup().get(refID);
                    }
                    ClusterRecord cr2 = repository.getEntityMap().getCluster(oysterID);
                    minOysterID = repository.getMinOysterID(cr, cr2);
                    
                    if (minOysterID.equals(cr2.getOysterID())){
                        cr = cr2;
                    }
                }
                minCR = repository.getEntityMap().getCluster(minOysterID);
            } else if (consolidate.size() == 1) {
                for (Iterator<Entry<String, String>> it = consolidate.entrySet().iterator(); it.hasNext();) {
                    Entry<String, String> entry = it.next();

                    String oysterID = repository.getLinkMap().get(entry.getKey());

                    if (oysterID == null) {
                        oysterID = repository.getRefIDLookup().get(entry.getKey());
                    }

                    minOysterID = oysterID;
                }
                minCR = repository.getEntityMap().getCluster(minOysterID);
            } else {
                // this is here just in case neagtive assertions remove all the candidates
                minOysterID = repository.getNextID(clusterRecord.getMergedRecord(), false);
                clusterRecord.setOysterID(minOysterID);
                minCR = clusterRecord.clone();
            }
            
            Set<String> rset = new LinkedHashSet<String>();
            for (Iterator<Entry<String, String>> it = consolidate.entrySet().iterator(); it.hasNext();) {
                Entry<String, String> entry = it.next();
                rule = consolidate.get(entry.getKey());
                rset.add(rule);
                
                String oysterID = repository.getLinkMap().get(entry.getKey());

                if (oysterID == null) {
                    oysterID = repository.getRefIDLookup().get(entry.getKey());
                }
                
                cr = repository.getEntityMap().getCluster(oysterID);

                if (logger.isLoggable(Level.INFO)) {
                    StringBuilder sb = new StringBuilder(100);
                    sb.append(System.getProperty("line.separator"))
                      .append("\tSatisfies Rule ").append(rule);
                    logger.info(sb.toString());
                }

                if (cr != null && !cr.getOysterID().equals(minCR.getOysterID())) {
                    // merge with the min ci
                    Set<String> set = new LinkedHashSet<String>();
                    set.add(rule);
                    minCR.merge(cr, repository.getMid(), set, repository.isTraceOn());
                    
                    if (cr.isPersistant()){
                        minCR.setPersistant(true);
                        
                        if (minCR.getCreationDate() == null) {
                            minCR.setCreationDate(cr.getCreationDate());
                        }
                        
                        if (minCR.getCreationDate().after(cr.getCreationDate())) {
                            minCR.setCreationDate(cr.getCreationDate());
                    }
                }
            }
            }
            minCR.merge(clusterRecord, repository.getMid(), rset, repository.isTraceOn());

            if (capture) {
//                cr = minCR.clone();
                repository.updateIdentity(minOysterID, minCR);
                
                // remove the merged clusters from the entity map
                for (Iterator<String> it = consolidate.keySet().iterator(); it.hasNext();) {
                    String refID = it.next();
                    String oysterID = repository.getLinkMap().get(refID);

                    if (oysterID == null) {
                        oysterID = repository.getRefIDLookup().get(refID);
                    }

                    if (!minOysterID.equals(oysterID)) {
                        repository.getEntityMap().removeCluster(oysterID);
                    }
                }

                repository.addIndex(minCR, mergedList);
                // update Link Map
                Set<String> s = minCR.getField("@RefID");
                for (Iterator<String> it = s.iterator(); it.hasNext();) {
                    String refID = it.next();

                    if (clusterRecord.getMergedRecord().get("@RefID").equals(refID)){
                        for (Iterator<String> it2 = rset.iterator(); it2.hasNext();){
                            repository.updateLink(refID, minOysterID, it2.next(), clusterRecord.getValuesByAttribute("@RefID"));
                        }
                    } else {
                        repository.updateLink(refID, minOysterID, "", clusterRecord.getValuesByAttribute("@RefID"));
                    }
                }
                
                if (logger.isLoggable(Level.INFO)) {
                    StringBuilder sb = new StringBuilder(500);
                    sb.append("\tAssign Entity ")
                      .append(index)
                      .append(" to Input ")
                      .append(recordCount)
                      .append(System.getProperty("line.separator"));
                    if (cr != null) {
                        sb.append("\tUpdate Entity: ")
                          .append(cr.getOysterID())
                          .append(" ")
                          .append(cr.getMergedRecord().toExplanationString())
                          .append(System.getProperty("line.separator"));
                    } else {
                        sb.append("\tUpdate Entity: ")
                          .append(cr.getOysterID())
                          .append(" ")
                          .append(clusterRecord.getMergedRecord().toExplanationString())
                          .append(System.getProperty("line.separator"));
                    }
                    sb.append("\t             : ")
                      .append(minCR.toString())
                      .append(System.getProperty("line.separator"));
                    sb.append("\tUpdate Index: ")
                      .append(index)
                      .append(" for ri ")
                      .append(clusterRecord.getMergedRecord())
                      .append(System.getProperty("line.separator"));
                    sb.append("\tUpdate LinkMap: ")
                      .append(minCR.getOysterID())
                      .append(" for ")
                      .append(s);
                    logger.info(sb.toString());
                }
            } else {
                for (int i = 0; i < minCR.getSize(); i++) {
                    OysterIdentityRecord oir = minCR.getOysterIdentityRecord(i);
                    rule = consolidate.get(oir.get("@RefID"));
                    repository.addLink(oir, minOysterID, rule);
                }
            }
            // I always count this but only use the counter in resolution mode
            resolvedRecords++;
        }
    }
    
    /**
     * This method take the <code>OysterIdentityRecord</code> candidate and compares it
     * to the current referenceItems to see if there is a partial rule match based
     * on the current rule list. All rules are processed at one time
     * @param candidate the <code>OysterIdentityRecord</code> candidate to be compared
     * @return true if at least one partial rule matched, otherwise false.
     */
    private boolean applyRules(OysterIdentityRecord candidate) {
        boolean matched = false;
        matrix.fill(false);

        // apply the rules
        for (Iterator<String> it = rules.keySet().iterator(); it.hasNext();) {
            String item = it.next();
            ArrayList<String> rule = rules.get(item);
            Set<String> compareToItems = compareTo.get(item);

            for (Iterator<String> it2 = rule.iterator(); it2.hasNext();) {
                String matchResult = it2.next();
                boolean flag;

                for (int z = 0; z < clusterRecord.getSize(); z++) {
                    OysterIdentityRecord oir = clusterRecord.getOysterIdentityRecord(z);
                    String source = oir.get(item);

                    OysterComparator compare = getAttributes().getComparator(item);
                    String target = candidate.get(item);

                    if (!(flag = compare(compare, source, target, matchResult))) {
                        if (compareToItems != null) {
                            for (Iterator<String> it3 = compareToItems.iterator(); it3.hasNext();) {
                                String secItem = it3.next();
                                source = oir.get(secItem);
                                if ((flag = compare(compare, source, target, matchResult))) {
                                    break;
                                }
                            }
                        }
                    }

                    // update the working Matrix
                    if (flag) {
                        matrix.getMatrix()[matrix.getRows().get(item)][matrix.getColumns().get(matchResult)] = flag;
                        matched = flag;
                    }
                }
            }
        }
        return matched;
    }

    /**
     * This method is not implemented in this class
     * @param sort
     * @param recordCount
     * @param countPoint
     */
    @Override
    public void postConsolidation(boolean sort, long recordCount, long countPoint) {
    }
}
