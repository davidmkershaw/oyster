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
 * new entity or same as an existing entity. This Engine uses the R-Swoosh 
 * methodology with inline consolidation. 
 * 
 * Responsibilities:
 * <ul>
 * <li>Apply resolution rules from reference source</li>
 * <li>Resolve reference</li>
 * </ul>
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.113E97B6-BB4E-5A4F-9555-9E31DB547978]
// </editor-fold> 
public class OysterMergeConsolidationEngine extends OysterResolutionEngine {
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.C3246F28-9E8A-B49F-B148-25190DA862CA]
    // </editor-fold> 
    /**
     * Creates a new instance of OysterMergeConsolidationEngine
     * @param logFile
     * @param logLevel
     */
    public OysterMergeConsolidationEngine (String logFile, Level logLevel, int recordType) {
        super(logFile, logLevel, recordType);
        mergedList = true;
        postConsolidation = true;
    }

    /**
     * Creates a new instance of OysterMergeConsolidationEngine
     * @param log
     */
    public OysterMergeConsolidationEngine (Logger log, int recordType) {
        super(log, recordType);
        mergedList = true;
        postConsolidation = true;
    }
    
    /**
     * Creates a new instance of OysterMergeConsolidationEngine
     */
    public OysterMergeConsolidationEngine (int recordType) {
        super(recordType);
        mergedList = true;
        postConsolidation = true;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.8AF348A3-E569-8286-703D-7C6023492F4C]
    // </editor-fold> 
    /**
     * This is the heart of the default <code>OysterMergeConsolidationEngine</code>. The
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
        boolean matched = false;
        int matchedCount = 0;
        ClusterRecord cr = null;
        long start = System.currentTimeMillis(), stop;
        
        if (logger.isLoggable(Level.INFO)) {
            StringBuilder sb = new StringBuilder(250);
            sb.append(System.getProperty("line.separator"))
              .append("Input: ")
              .append(clusterRecord.getMergedRecord());
            logger.info(sb.toString());
        }
/*        
        if (codosaIdentity.getValueByTag("B").equals("L1.27")){
            System.out.println();
        }
*/        
        
        // Ask IdentityRepository for a list of candidates
        Map<String, ClusterRecord> list;
        if ((list = repository.getCandidateList(clusterRecord, sort, primaryFilter, lcrdMinSize,isByPassFilter(), mergedList)).isEmpty()){
            if (secondaryFilter != null) {
                list = repository.getCandidateList(clusterRecord, sort, secondaryFilter, lcrdMinSize,isByPassFilter(), mergedList);
            }
        }
        
        totalCandidatesSize += list.size();
        
        // Remove duplicate Clusters
        list = removeDuplicateClusters(list);
        
        totalCandidatesDeDupSize += list.size();
        if (list.size() > 0) {
            totalCandidates++;
        }
        
        if (logger.isLoggable(Level.FINE)) {
            logger.fine("\tCandidate List:");
            for (Iterator<Entry<String, ClusterRecord>> it = list.entrySet().iterator(); it.hasNext();){
                Entry<String, ClusterRecord> entry = it.next();
                cr = entry.getValue();
                StringBuilder sb = new StringBuilder(250);
                sb.append("\t\t").append(entry.getKey())
                  .append("=").append(cr.getMergedRecord().toExplanationString());
                logger.fine(sb.toString());
            }
            logger.fine("");
        }
        
        String index = "", minIndex , rule = "";
        Map<String, String> consolidate = new LinkedHashMap<String, String>();
        ArrayList<String> prevOysterIDs = new ArrayList<String>();
        int identityCount = 1;
        for(Iterator<Entry<String, ClusterRecord>> it = list.entrySet().iterator(); it.hasNext();){
            Entry<String, ClusterRecord> entry = it.next();
            index = entry.getKey();
            cr = entry.getValue();
            
            if (logger.isLoggable(Level.INFO)) {
                StringBuilder sb = new StringBuilder(250);
                sb.append("\tCompare Input ")
                  .append(recordCount)
                  .append(" to Identity ")
                  .append(identityCount)
                  .append(" ")
                  .append(cr.getMergedRecord().toExplanationString());
                logger.info(sb.toString());
            }
            
            // check to see that I have not already looked at another version of
            // this record. This is need because of the consolidation. If not 
            // then apply the rules.
            Set<String> completeRules = new TreeSet<String>();
            if (!prevOysterIDs.contains(cr.getOysterID()) && applyRules(cr.getMergedRecord())){
                if (logger.isLoggable(Level.FINE)){
                    logger.fine("matrix");
                    logger.fine(matrix.toString());
                    logger.fine("");
                    logger.fine("masks");
               }
                
                // does the matrix match any of the masks
                for(Iterator<String> it2 = masks.keySet().iterator(); it2.hasNext();){
                    String key = it2.next();
                    Matrix m = masks.get(key);
                    
                    if (logger.isLoggable(Level.FINE)){
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
                        Logger.getLogger(OysterMergeConsolidationEngine.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
                    }
                    
                    // If the mask matches the temp rule then it's a match
                    if (m.equals(temp)) {
                        matched = true;

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
                        }
                        matchedCount++;
                    }
                }
                
                // check to see if this result can be consildated with a previous result
                if (matched){
                    consolidate.put(index, rule);
                    prevOysterIDs.add(cr.getOysterID());
                    if (capture) {
                        matched = false;
                    }
                    // break;
                }
            }
            
            if (matched){
                break;
            }
            identityCount++;
        }
        stop = System.currentTimeMillis();
        
        // Do I need to consolidated?
        // FIXME: Should this be 0 or 1? 0 seems to work better. Why?
        if (consolidate.size() > 0){
            minIndex = inlineConsolidation(consolidate);
        } else {
            minIndex = index;
        }
        
        // reset matched flag and get the matched index
        if (consolidate.size() > 0){
//            index = (String) consolidate.keySet().toArray()[0];
            matched = true;
        }
        
        // FIXME: How do I want to handle a merge-purge only run? 
        // Should be a run with capture mode off and no identity input. One way 
        // would be to use the inverted index but this could possibly cause a 
        // problem by bringing records together due to the index. I will have to
        // test this extensively.
        
        // Ask IdentityRespository to update/create identity
        if (minIndex != null) {
            manageEntity(cr, index, rule, matched, recordCount, minIndex, consolidate);
        } else {
            System.out.println("Null index in Candidate List!!!");
            if (logger.isLoggable(Level.INFO)) {
                logger.info("Null index in Candidate List!!!");
            }
        }
        
        if (matched && logger.isLoggable(Level.FINEST)){
            dump();
        }
        
        // do the latency stats
        long latency = stop - start;
        if (matched){
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
     * @param index the RefID number tah was matched  (can be empty is not matched)
     * @param rule the rule that was matched on (can be empty is not matched)
     * @param match whether the input record matched a candidate record or not
     * @param recordCount the current record count
     * @param minIndex the RefID found based on the "min" OysterID (can be empty 
     * is not matched)
     * @param consolidate a list of all the candidates that were found to match 
     * (can be empty is not matched)
     */
    private void manageEntity(ClusterRecord cr, String index, String rule, boolean match, long recordCount, String minIndex, Map<String, String> consolidate){
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

//                repository.addIndex(cr, mergedList);
                repository.addIndex(cr, true);
                repository.addLink(cr.getMergedRecord(), id, rule);
                    
                if (logger.isLoggable(Level.INFO)) {
                    StringBuilder sb = new StringBuilder(250);
                    sb.append("\tNew Entity ")
                      .append(cr.getOysterID())
                      .append(" ")
                      .append(cr.getMergedRecord().toExplanationString())
                      .append(System.getProperty("line.separator"));
                    sb.append("\tNew Index: ")
                      .append(cr.getMergedRecord())
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
                    StringBuilder sb = new StringBuilder(250);
                    sb.append("\tNo Capture: LinkMap{")
                      .append(cr.getMergedRecord().get("@RefID"))
                      .append("}, ")
                      .append(cr.getMergedRecord().toExplanationString());
                    logger.info(sb.toString());
                }
            }
        } else if (match) {
            if (minIndex != null) {
                String oysterID = repository.getLinkMap().get(minIndex);
                ClusterRecord minCR = repository.getEntityMap().getCluster(oysterID);
                oysterID = minCR.getOysterID();

                for (Iterator<Entry<String, String>> it = consolidate.entrySet().iterator(); it.hasNext();) {
                    Entry<String, String> entry = it.next();
                    rule = entry.getValue();
                    String key = repository.getLinkMap().get(entry.getKey());
                    cr = repository.getEntityMap().getCluster(key);

                    if (cr != null) {
                        if (logger.isLoggable(Level.INFO)) {
                            logger.info("");
                            StringBuilder sb = new StringBuilder(100);
                            sb.append("\tSatisfies Rule: ").append(rule);
                            logger.info(sb.toString());
                        }

                        String token = cr.getOysterID();

                        if (!token.equals(oysterID)) {
                            // Update entityMap
                            cr.setOysterID(oysterID);

                            // merge with the min ci
                            LinkedHashSet<String> set = new LinkedHashSet<String>();
                            set.add(rule);
                            minCR.merge(cr, repository.getMid(), set, repository.isTraceOn());
                        }
                    } else {
                        String s = "Index: " + entry.getKey() + " retrieved " + key + " from the LinkMap that can not be found in the repository.";
                        System.out.println(s);
                        logger.severe(s);
                    }
                }
                
                if (capture) {
                    // output the merged ci to the temp file
                    Set<String> set = new LinkedHashSet<String>();
                    set.add(rule);
                    repository.updateEntitySet(clusterRecord, minCR, oysterID, set);
                    repository.getEntityMap().removeCluster(oysterID);
                    
                    if (cr != null) {
                        repository.removeIndex(cr.getMergedRecord(), index);
                    } else {
                        repository.removeIndex(clusterRecord.getMergedRecord(), index);
                    }
                    
                    if (logger.isLoggable(Level.INFO)) {
                        StringBuilder sb = new StringBuilder(1000);
                        sb.append("\tAssign Entity ").append(index).append(" to Input ").append(recordCount);
                        sb.append(System.getProperty("line.separator"));

                        if (cr != null) {
                            sb.append("\tUpdate Entity: ")
                              .append(cr.getOysterID())
                              .append(" ")
                              .append(cr.getMergedRecord().toExplanationString());
                        } else {
                            sb.append("\tUpdate Entity: ")
                              .append(cr.getOysterID())
                              .append(" ")
                              .append(clusterRecord.getMergedRecord().toExplanationString());
                        }
                        sb.append(System.getProperty("line.separator"));
                        sb.append("\t             : ").append(minCR.toString());
                        logger.info(sb.toString());
                    }

                    // update Link Map
                    Set<String> s = minCR.getField("@RefID");
                    for (Iterator<String> it = s.iterator(); it.hasNext();) {
                        String refID = it.next();
                        rule = consolidate.get(refID);
                        repository.updateLink(refID, oysterID, rule, clusterRecord.getValuesByAttribute("@RefID"));
                    }

                    if (logger.isLoggable(Level.INFO)) {
                        StringBuilder sb = new StringBuilder(1000);
                        sb.append("\tUpdate Index: ")
                          .append(index)
                          .append(" for ri ")
                          .append(clusterRecord.getMergedRecord())
                          .append(System.getProperty("line.separator"));
                        sb.append("\tUpdate LinkMap: ")
                          .append(minCR.getOysterID())
                          .append(" for ")
                          .append(s)
                          .append(System.getProperty("line.separator"));
                        logger.info(sb.toString());
                    }
                } else {
                    repository.addLink(minCR.getMergedRecord(), minCR.getOysterID(), rule);
                }
                // I always count this but only use the counter in resolution mode
                resolvedRecords++;
            } else {
                System.out.println("Inline Consolidation probelm Null minIndex returned.");
                if (logger.isLoggable(Level.INFO)) {
                    logger.info("Inline Consolidation probelm Null minIndex returned.");
                }
            }
        }
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.420C2439-C6B7-3B04-09BF-B5559976D406]
    // </editor-fold> 
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
        OysterIdentityRecord oir = clusterRecord.getMergedRecord();

        for (Iterator<String> it = rules.keySet().iterator(); it.hasNext();) {
            String item = it.next();
            ArrayList<String> rule = rules.get(item);
            Set<String> compareToItems = compareTo.get(item);

            for (Iterator<String> it2 = rule.iterator(); it2.hasNext();) {
                String matchResult = it2.next();
                boolean flag;

                String source = oir.get(item);

                // get the comparator for this rule term
                OysterComparator compare = getAttributes().getComparator(item);
                String target = candidate.get(item);
                if (compare != null) {
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
                        break;
                    }
                }
            }
        }
        return matched;
    }

    // FIXME: Do I need to remove the changed CI's from the enitityMap and replace the with a consolidated minCI?
    /**
     * Inline Consolidation is the process of consolidate records that are the 
     * same entity but have been give different OysterID's because the order in which 
     * there were processed was important. The minimum OysterId is determined and
     * the OysterID's of the remaining records are changed to this value. The link
     * record for each record is removed from the linkMap. Currently, the multiple
     * records are left in the entityMap. A future consideration would be to remove
     * these from the entityMap then merge these all into one single <code>
     * ClusterRecord</code> and insert it into the entityMap.
     * @param m Map of RefID's and rule match number
     * @return minimum OysterID
     */
    private String inlineConsolidation(Map<String, String> m) {
        ClusterRecord cr, minCR = null;
        int min = Integer.MAX_VALUE;
        String minIndex = "";
        StringBuilder log = new StringBuilder(250);
        boolean persistant = false;

        // check and see if there is at least one persistant record
        for (Iterator<String> it = m.keySet().iterator(); it.hasNext();) {
            String key = it.next();

            String oysterID = repository.getLinkMap().get(key);
            cr = repository.getEntityMap().getCluster(oysterID);

            if (cr != null) {
                if (cr.isPersistant()) {
                    persistant = true;
                }
            }
        }

        // get the minimum OysterID value
        for (Iterator<String> it = m.keySet().iterator(); it.hasNext();) {
            String key = it.next();

            String oysterID = repository.getLinkMap().get(key);
            cr = repository.getEntityMap().getCluster(oysterID);

            if (cr != null) {
                if (persistant) {
                    if (cr.getOysterID().hashCode() < min && cr.isPersistant()) {
                        min = cr.getOysterID().hashCode();
                        minCR = cr;
                        minIndex = key;
                    }
                } else {
                    if (cr.getOysterID().hashCode() < min) {
                        min = cr.getOysterID().hashCode();
                        minCR = cr;
                        minIndex = key;
                    }
                }
            } else {
                System.out.println("Null CR for key: " + key);
            }
        }

        log.append("\tConsolidating : ").append(minIndex).append(" --> ");

        if (minCR != null) {
            for (Iterator<String> it = m.keySet().iterator(); it.hasNext();) {
                String key = it.next();
                String oysterID = repository.getLinkMap().get(key);
                cr = repository.getEntityMap().getCluster(oysterID);

                if (cr != null) {
                    if (!cr.getOysterID().equals(minCR.getOysterID())) {
                        log.append(key).append("|");

                        // Update entityMap
                        cr.setOysterID(minCR.getOysterID());
                        repository.addNewIdentity(key, cr);

                        // Update linkMap
                        Set<String> s = cr.getField("@RefID");
                        for (Iterator<String> it2 = s.iterator(); it2.hasNext();) {
                            String refID = it2.next();
                            repository.getLinkMap().put(refID, minCR.getOysterID());
                        }
                    }
                }
            }

            if (logger.isLoggable(Level.INFO)) {
                if (log.toString().endsWith("|")) {
                    log = log.deleteCharAt(log.length() - 1);
                }
                logger.info(log.toString());
            }
        } else {
            minIndex = null;
        }

        return minIndex;
    }
    
    /**
     * This method implements the R-Swoosh methodology. R-Swooshing will continue
     * until the Entity Set is empty
     * @param sort true if the candidate list should be sorted desc on the most
     * frequently occuring candidates
     */
    @Override
    public void postConsolidation(boolean sort, long recordCount, long countPoint) {
        long count = 0;
        
        System.out.println("RSwooshing...");
        logger.info("## STARTING RSWOOSH ##");
        
        // rebuild it fully populated
        for (Iterator<ClusterRecord> it = repository.getEntitySet().iterator(); it.hasNext();){
            ClusterRecord cr = it.next();
            for (int i = 0; i < cr.getSize(); i++){
                OysterIdentityRecord oir = cr.getOysterIdentityRecord(i);
                repository.addIndex(oir);
            }
        }
        
        if (logger.isLoggable(Level.FINEST)){
            dump();
        }
        
        while (!repository.getEntitySet().isEmpty()) {
            clusterRecord = repository.getEntitySet().iterator().next();
            repository.getEntitySet().remove(clusterRecord);

            integrateSource (sort, count++);
            
            if (count % countPoint == 0) {
                System.out.println("RS-" + count + "...");
            }
            tempCounter++;
        }
        logger.info("## ENDING RSWOOSH ##");
    }
}
                                                        
