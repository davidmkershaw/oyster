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
import edu.ualr.oyster.association.matching.OysterComparator;
import edu.ualr.oyster.core.OysterAttributes;
import edu.ualr.oyster.core.OysterRule;
import edu.ualr.oyster.core.ReferenceItem;
import edu.ualr.oyster.core.RuleTerm;
import edu.ualr.oyster.data.ClusterRecord;
import edu.ualr.oyster.data.ClusterRecordSet;
import edu.ualr.oyster.data.CoDoSAOIR;
import edu.ualr.oyster.data.OysterIdentityRecord;
import edu.ualr.oyster.data.OysterIdentityRecordMap;
import edu.ualr.oyster.data.RecordTypes;
import edu.ualr.oyster.optimization.Matrix;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * OysterResolutionEngine.java
 * Created on Nov 13, 2010 12:33:54 AM
 * @author Eric D. Nelson
 */
public abstract class OysterResolutionEngine extends OysterEngine{
    /** The Oyster attributes that are used for this ER engine */
    protected OysterAttributes attributes = null;

    /** The primary LCRD filter that are used for this ER engine */
    protected Map<Integer, ArrayList<String>> primaryFilter = null;
    
    /** The secondary LCRD filter that are used for this ER engine */
    protected Map<Integer, ArrayList<String>> secondaryFilter = null;
    
    /** The size of the smallest filter */
    protected int lcrdMinSize = Integer.MAX_VALUE;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.FD6BD4A0-B04B-DBAA-07ED-8D518606EAA7]
    // </editor-fold> 
    /** The Oyster Rules that are used for this ER engine */
    protected ArrayList<OysterRule> ruleList = null;

    /** */
    protected boolean mergedList = false;
    
    /** */
    protected String tempFile = "";
    
    /** the current counter */
    protected long tempCounter = 0;
    
    /**
     * This flag is used to determine if the ER engine being used is has a post
     * consolidation methodology.
     */
    protected boolean postConsolidation = false;
    
    /** The rules Matrix workspace */
    protected Matrix matrix = null;
    
    /** The matrix masks for each rule */
    protected Map<String, Matrix> masks = null;
    
    /** */
    protected Map<String, ArrayList<String>> rules = null;
    
    /** */
    protected Map<String, Set<String>> compareTo = null;

    /** contains the first rule that fired */
    protected Map<String, Long> ruleFreq = null;

    /** contains a complete firing of all rules */
    protected Map<String, Long> completeRuleFiring;
    
    /** */
    protected PrintWriter out = null;
    
    /** */
    protected boolean byPassFilter = true;
    
    /**
     * Creates a new instance of OysterResolutionEngine
     */
    public OysterResolutionEngine(int recordType){
        super();
        
        this.recordType = recordType;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.C3246F28-9E8A-B49F-B148-25190DA862CA]
    // </editor-fold> 
    /**
     * Creates a new instance of OysterResolutionEngine
     * @param logFile
     * @param logLevel
     */
    public OysterResolutionEngine (String logFile, Level logLevel, int recordType) {
        super();
        
        this.recordType = recordType;
        
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
            Logger.getLogger(OysterResolutionEngine.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch (IOException ex) {
            Logger.getLogger(OysterResolutionEngine.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }

    /**
     * Creates a new instance of OysterResolutionEngine
     * @param log
     */
    public OysterResolutionEngine (Logger log, int recordType) {
        super();
        
        this.recordType = recordType;
        
        try {
            // initialize logger
            this.logger = log;
        } catch (SecurityException ex) {
            Logger.getLogger(OysterResolutionEngine.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }
    
    /**
     * Returns the <code>OysterAttributes</code> for this engine.
     * @return the <code>OysterAttributes</code>.
     */
    public OysterAttributes getAttributes () {
        return attributes;
    }

    /**
     * Sets the <code>OysterAttributes</code> for this engine.
     * @param attributes the <code>OysterAttributes</code> to be set.
     */
    public void setAttributes (OysterAttributes attributes) {
        this.attributes = attributes;
    }
    
    /**
     * Returns the primary Least Common Rule Denominator filter for the engine.
     * @return the engines rule filter.
     */
    public Map<Integer, ArrayList<String>> getPrimaryFilter() {
        return primaryFilter;
    }

    /**
     * Sets the primary Least Common Rule Denominator filter for the engine.
     * @param primaryFilter rule filter to be set.
     */
    public void setPrimaryFilter(Map<Integer, ArrayList<String>> primaryFilter) {
        this.primaryFilter = primaryFilter;
        
        for (Iterator<Integer> it = this.primaryFilter.keySet().iterator(); it.hasNext();) {
            int key = it.next();
            ArrayList<String> value = this.primaryFilter.get(key);
            lcrdMinSize = Math.min(lcrdMinSize, value.size());
        }
    }
    
    /**
     * Returns the secondary Least Common Rule Denominator filter for the engine.
     * @return the engines rule filter.
     */
    public Map<Integer, ArrayList<String>> getSecondaryFilter() {
        return secondaryFilter;
    }

    /**
     * Sets the secondary Least Common Rule Denominator filter for the engine.
     * @param secondaryFilter rule filter to be set.
     */
    public void setSecondaryFilter(Map<Integer, ArrayList<String>> secondaryFilter) {
        this.secondaryFilter = secondaryFilter;
        
        for (Iterator<Integer> it = this.secondaryFilter.keySet().iterator(); it.hasNext();) {
            int key = it.next();
            ArrayList<String> value = this.secondaryFilter.get(key);
            lcrdMinSize = Math.min(lcrdMinSize, value.size());
        }
    }

    /**
     * Returns the size of the smallest LCRD filter
     * @return the min filter size
     */
    public int getLcrdMinSize() {
        return lcrdMinSize;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.FF26CB6F-4032-10EB-0D96-BA1FBE3B4729]
    // </editor-fold> 
    /**
     * Returns the rule list for this engine.
     * @return a list of <code>OysterRules</code>.
     */
    public ArrayList<OysterRule> getRuleList () {
        return ruleList;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.58FFDBC5-B802-E69A-FFCC-4F89285A6DD2]
    // </editor-fold> 
    /**
     * Sets the rule list for this engine.
     * @param ruleList the <code>ArrayList</code> of rules to be used by the engine.
     */
    public void setRuleList (ArrayList<OysterRule> ruleList) {
        this.ruleList = ruleList;
    }

    /**
     * Sets the engines list of <code>OysterIdentityRecord</code>.
     * @param oir the <code>OysterIdentityRecord</code> of items to be integrated.
     */
    public void setClusterRecord (OysterIdentityRecord oir) {
        if(clusterRecord == null) {
            clusterRecord = new ClusterRecordSet(this.recordType);
        }
        clusterRecord.insertRecord(oir);
    }
    
    /**
     * Sets the engines list of <code>ReferenceItem</code>.
     * @param referenceItems the list of <code>ReferenceItems</code> to be 
     * integrated.
     */
    public void setClusterRecord (ArrayList<ReferenceItem> referenceItems) {
        OysterIdentityRecord oir;
        
        switch(this.recordType){
            case RecordTypes.CODOSA:
                oir = new CoDoSAOIR();
                break;
            case RecordTypes.MAP:
                oir = new OysterIdentityRecordMap();
                break;
            default:
                oir = new OysterIdentityRecordMap();
        }
        oir.convertToOIR(referenceItems);
        clusterRecord.insertRecord(oir);
    }
    
    /**
     * Returns whether the merge list flag is set
     * @return true if the mergeList flag is set, otherwise false
     */
    public boolean isMergedList() {
        return mergedList;
    }

    /**
     * Sets the merge list
     * @param mergedList the merge list to be set
     */
    public void setMergedList(boolean mergedList) {
        this.mergedList = mergedList;
    }
    
    /**
     * Returns the current temp filename for the source being integrated by the
     * engine.
     * @return tempFile
     */
    public String getTempFile() {
        return tempFile;
    }

    /**
     * Sets the current temp filename for the source being integrated by the
     * engine.
     * @param tempFile the temp filename to be set.
     */
    public void setTempFile(String tempFile) {
        this.tempFile = tempFile;
    }
    
    /**
     * Returns the current temp count 
     * @return tempCounter
     */
    public long getTempCounter() {
        return tempCounter;
    }

    /**
     * Set the temp counter
     * @param tempCounter the temp counter to be set.
     */
    public void setTempCounter(long tempCounter) {
        this.tempCounter = tempCounter;
    }
    
    /**
     * Returns whether the engine has a post Consolidation method.
     * @return true if the engine has a post Consolidation method, otherwise false.
     */
    public boolean hasPostConsolidation () {
        return postConsolidation;
    }
    
    /**
     * Returns the current rule frequency
     * @return ruleFreq
     */
    public Map<String, Long> getRuleFreq() {
        return ruleFreq;
    }

    /**
     * Sets the rule frequency
     * @param ruleFreq the rule frequency to be set
     */
    public void setRuleFreq(Map<String, Long> ruleFreq) {
        this.ruleFreq = ruleFreq;
    }

    /**
     * @return the completeRuleFiring
     */
    public Map<String, Long> getCompleteRuleFiring() {
        return completeRuleFiring;
    }

    /**
     * @param completeRuleFiring the completeRuleFiring to set
     */
    public void setCompleteRuleFiring(Map<String, Long> completeRuleFiring) {
        this.completeRuleFiring = completeRuleFiring;
    }

    public boolean isByPassFilter() {
        return byPassFilter;
    }

    public void setByPassFilter(boolean byPassFilter) {
        this.byPassFilter = byPassFilter;
    }
    
    /**
     * The method creates a <code>Matrix</code> based on the current rules and Attribute
     * settings for the engine and sets everything in the Matrix square to false.
     */
    public void createMatrix(){
        matrix = new Matrix();
        
        ArrayList<String> items = new ArrayList<String>();
        ArrayList<String> results = new ArrayList<String>();
        int row = 0, col = 0;
        
        // get the number of items & match results
        for (Iterator<OysterRule> it = ruleList.iterator(); it.hasNext();){
            OysterRule or = it.next();
            
            // get the items from the attribute list and place one in each row
            for(Iterator<RuleTerm> it2 = or.getTermList().iterator(); it2.hasNext();){
                RuleTerm item = it2.next();
                
                if (!items.contains(item.getItem())){
                    items.add(item.getItem());
                    
                    matrix.getRows().put(item.getItem(), row);
                    row++;
                }
                
                // get the operations from the attribute list and place one in each column
                Set<RuleTerm> values = or.getTermList();
                for (Iterator<RuleTerm> it3 = values.iterator(); it3.hasNext();){
                    RuleTerm key = it3.next();
                    
                    if (!results.contains(key.getMatchResult())){
                        results.add(key.getMatchResult());
                        
                        matrix.getColumns().put(key.getMatchResult(), col);
                        col++;
                    }
                }
            }
        }
        
        // Initialize the Matrix to false
        matrix.setMatrix(new boolean[items.size()][results.size()]);
        matrix.fill(false);
    }
    
    /**
     * This method produces the <code>Matrix</code> masks that are used to see if
     * a record has passed a particular rule. There will be one mask per each rule.
     */
    public void populateMasks(){
        masks = new LinkedHashMap<String, Matrix>();
        rules = new LinkedHashMap<String, ArrayList<String>>(); 
        compareTo = new LinkedHashMap<String, Set<String>>();
        
        // iterator over the rule list to get each rule
        System.out.println(ruleList);
        for (Iterator<OysterRule> it = ruleList.iterator(); it.hasNext();){
            OysterRule or = it.next();
            
            // create an empty mask
            Matrix m = null;
            try {
                m = (Matrix) matrix.clone();
                
                // for each rule populate the [item][matchResult] with a true
                for (Iterator<RuleTerm> it2 = or.getTermList().iterator(); it2.hasNext();) {
                    RuleTerm item = it2.next();

                    m.getMatrix()[m.getRows().get(item.getItem())][m.getColumns().get(item.getMatchResult())] = true;

                    ArrayList<String> al = rules.get(item.getItem());
                    if (al == null) {
                        al = new ArrayList<String>();
                    }

                    if (!al.contains(item.getMatchResult())) {
                        al.add(item.getMatchResult());
                    }
                    rules.put(item.getItem(), al);
                    
                    if (item.getCompareTo() != null) {
                        compareTo.put(item.getItem(), item.getCompareTo());
                    }
                }
   
            } catch (CloneNotSupportedException ex) {
                Logger.getLogger(OysterResolutionEngine.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
            }
            
            masks.put(or.getRuleIdentifer(), m);
        }
    }
    
    public abstract void integrateSource (boolean sort, long recordCount);
    
    public abstract void postConsolidation(boolean sort, long recordCount, long countPoint);
    
    protected boolean compare(OysterComparator compare, String source, String target, String matchResult) {
        boolean flag = false;

        if (compare != null) {
            String[] target2, source2;

            if (target != null) {
                target2 = target.split("[|]");
            } else {
                target2 = "".split("");
            }

            if (source != null) {
                source2 = source.split("[|]");
            } else {
                source2 = "".split("");
            }

            for (int i = 0; i < target2.length; i++) {
                for (int j = 0; j < source2.length; j++) {
                    String result = compare.compare(source2[j], target2[i], matchResult);

                    if (matchResult.equalsIgnoreCase(result)) {
                        flag = true;
                        break;
                    }
                }

                if (flag) {
                    break;
                }
            }
        }

        return flag;
    }
    
    /**
     * Checks the LinkMap for any unresolved non-persistent records. If found set
     * the the OysterID to "XXXXXXXXXXXXXXXX"
     */
    public void unResolvedRecordFix(){
        for (Iterator<String> it = repository.getLinkMap().keySet().iterator(); it.hasNext();){
            String refID = it.next();
            String oysterID = repository.getLinkMap().get(refID);
            
            ClusterRecord cr = repository.getEntityMap().getCluster(oysterID);
            
            if (!cr.isPersistant()){
                oysterID = "XXXXXXXXXXXXXXXX";
                repository.getLinkMap().put(refID, oysterID);
            }
        }
    }
    
    /**
     * Memory Dump of the Entity Map, Entity Set, Value Index, and Link Map
     */
    @SuppressWarnings( "unchecked" )
    public void dump(){
        StringBuilder sb = new StringBuilder(1000);
        sb.append(System.getProperty("line.separator"))
          .append("**** DUMP START ****");
        sb.append(System.getProperty("line.separator"))
          .append("entityMap");
        for (Iterator<String> it = repository.getEntityMap().getData().keySet().iterator(); it.hasNext();){
            String key = it.next();
            ClusterRecord cr = repository.getEntityMap().getCluster(key);
            sb.append(System.getProperty("line.separator"))
              .append(key)
              .append("\t")
              .append(cr.toString());
        }
        sb.append(System.getProperty("line.separator"));
        
        sb.append("entitySet");
        for (Iterator<ClusterRecord> it = repository.getEntitySet().iterator(); it.hasNext();){
            ClusterRecord cr = it.next();
            sb.append(System.getProperty("line.separator"))
              .append(cr.toString());
        }
        sb.append(System.getProperty("line.separator"));
        
        sb.append("valueIndex");
        if (repository.getValueIndex().getClass().getSimpleName().equals("DBIndex")){
            
        } else {
            for (Iterator<String> it = repository.getValueIndex().getIterator(); it.hasNext();){
                String key = it.next();
                Set<String> s = (Set<String>) repository.getValueIndex().get(key);
                sb.append(System.getProperty("line.separator"))
                  .append(key)
                  .append("\t")
                  .append(s);
            }
        }
        sb.append(System.getProperty("line.separator"));
        
        sb.append("linkMap");
        for (Iterator<String> it = repository.getLinkMap().keySet().iterator(); it.hasNext();){
            String key = it.next();
            String value = repository.getLinkMap().get(key);
            sb.append(System.getProperty("line.separator"))
              .append(key)
              .append("\t")
              .append(value);
        }
        sb.append(System.getProperty("line.separator"));
        sb.append("**** DUMP END ****")
          .append(System.getProperty("line.separator"));
        logger.info(sb.toString());
    }
    
    /**
     * This method removes any clusters that may be duplicates. This is due to a
     * cluster having multiple refID's (many to one relationship)
     * @param list input list of candidates
     * @return input candidate list with duplicates removed
     */
    protected Map<String, ClusterRecord> removeDuplicateClusters(Map<String, ClusterRecord> list) {
        Map<String, ClusterRecord> result = new LinkedHashMap<String, ClusterRecord>();
        for (Iterator<Entry<String, ClusterRecord>> it = list.entrySet().iterator(); it.hasNext();){
            Entry<String, ClusterRecord> entry = it.next();
            ClusterRecord cr = entry.getValue();
            it.remove();
            
            // if the list does not contain another instance of the ClusterRecord read
            if (!list.containsValue(cr)) {
                result.put(entry.getKey(), cr);
            }
        }
        return result;
    }
}
