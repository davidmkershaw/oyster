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
 * methodology.
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
public class OysterMergeEngine extends OysterResolutionEngine {
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.C3246F28-9E8A-B49F-B148-25190DA862CA]
    // </editor-fold> 
    /**
     * Creates a new instance of OysterMergeEngine
     * @param logFile
     * @param logLevel
     */
    public OysterMergeEngine (String logFile, Level logLevel, int recordType) {
        super(logFile, logLevel, recordType);
        mergedList = true;
        postConsolidation = true;
    }

    /**
     * Creates a new instance of OysterMergeEngine
     * @param log
     */
    public OysterMergeEngine (Logger log, int recordType) {
        super(log, recordType);
        mergedList = true;
        postConsolidation = true;
    }
    
    /**
     * Creates a new instance of OysterMergeEngine
     */
    public OysterMergeEngine (int recordType) {
        super(recordType);
        mergedList = true;
        postConsolidation = true;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.8AF348A3-E569-8286-703D-7C6023492F4C]
    // </editor-fold> 
    /**
     * This is the heart of the default <code>OysterMergeEngine</code>. The
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
        ClusterRecord cr;
        long start = System.currentTimeMillis(), stop;
        
        if (logger.isLoggable(Level.INFO)) {
            StringBuilder sb = new StringBuilder(250);
            sb.append(System.getProperty("line.separator"))
              .append("Input: ")
              .append(clusterRecord.getMergedRecord());
            logger.info(sb.toString());
        }
//        System.out.println("Input: "  + clusterRecord.getMergedRecord());
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
        
        String matchedIndex = "", rule = "";
        int identityCount = 1;
        for(Iterator<Entry<String, ClusterRecord>> it = list.entrySet().iterator(); it.hasNext();){
            Entry<String, ClusterRecord> entry = it.next();
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
            if (!matched && applyRules(cr.getMergedRecord())){
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
                        Logger.getLogger(OysterMergeEngine.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
                    }
                    
                    // If the mask matches the temp rule then it's a match
                    if (m.equals(temp)){
                        matched = true;
                        long value = 0;
                        if (completeRuleFiring.containsKey(completeRules.toString())) {
                            value = completeRuleFiring.get(completeRules.toString());
                        }
                        value++;
                        completeRuleFiring.put(completeRules.toString(), value);

                        if (matchedCount == 0) {
                            matchedIndex = entry.getKey();
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
            }
            
            if (matched){
                break;
            }
            identityCount++;
        }
        stop = System.currentTimeMillis();
        
        // Ask IdentityRespository to update/create identity
        if (matchedIndex != null){
            manageEntity(matchedIndex, rule, matched, recordCount);
        } else {
            System.out.println("Null index in Candidate List!!!");
            if (logger.isLoggable(Level.INFO)){
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

//                System.out.println("EntityMap: "  + repository.getEntityMap() + System.getProperty("line.separator"));
        //               System.out.println("LinkMap  : "  + repository.getLinkMap() + System.getProperty("line.separator"));
        } else if (match) {
            if (logger.isLoggable(Level.INFO)) {
                logger.info("");
                StringBuilder sb = new StringBuilder(100);
                sb.append("\tSatisfies Rule: ").append(rule);
                logger.info(sb.toString());
            }
            String oysterID = repository.getLinkMap().get(index);

            if (oysterID == null) {
                oysterID = repository.getRefIDLookup().get(index);
            }
            cr = repository.getEntityMap().getCluster(oysterID);

            if (capture) {
                LinkedHashSet<String> set = new LinkedHashSet<String>();
                set.add(rule);
                String id = repository.updateEntitySet(clusterRecord, cr, oysterID, set);
                
                if (cr != null) {
                    repository.removeIndex(cr.getMergedRecord(), index);
                    repository.addLink(cr.getMergedRecord(), id, rule);
                    repository.addLink(clusterRecord.getMergedRecord(), id, rule);
                } else {
                    repository.removeIndex(clusterRecord.getMergedRecord(), index);
                    repository.addLink(clusterRecord.getMergedRecord(), id, rule);
                }

                repository.getEntityMap().removeCluster(oysterID);

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
                          .append(clusterRecord.getOysterID())
                          .append(" ")
                          .append(clusterRecord.getMergedRecord().toExplanationString());
                }
                    sb.append(System.getProperty("line.separator"));
                    sb.append("\tUpdate Index: ")
                      .append(index)
                      .append(" for ri ")
                      .append(clusterRecord.getMergedRecord())
                      .append(System.getProperty("line.separator"));
                    logger.info(sb.toString());
                }
            } else {
                // repository.addLink(codosaIdentity, ci.getValueByTag("A"), rule);
                repository.addLink(clusterRecord.getMergedRecord(), oysterID, rule);
            }
            // I always count this but only use the counter in resolution mode
            resolvedRecords++;
//                System.out.println("EntityMap: "  + repository.getEntityMap() + System.getProperty("line.separator"));
//                System.out.println("LinkMap  : "  + repository.getLinkMap() + System.getProperty("line.separator"));
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

    /**
     * This method implements the R-Swoosh methodology. R-Swooshing will continue
     * until the Entity Set is empty
     * @param sort true if the candidate list should be sorted desc on the most
     * frequently occurring candidates
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
                                                        
