/*
 * Copyright 2012 John Talburt, Eric Nelson
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

import edu.ualr.oyster.data.ClusterRecord;
import edu.ualr.oyster.data.ClusterRecordSet;
import edu.ualr.oyster.data.OysterIdentityRecord;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * EntityMap.java
 * Created on Sep 9, 2011 11:13:40 PM
 * @author Eric D. Nelson
 */
public class EntityMap {
    /** The data for the <code>EntityMap</code> */
    protected Map<String, ClusterRecord> data = null;
    
    protected int recordType = 0;
    
    /**
     * Creates a new instance of <code>EntityMap</code>
     */
    public EntityMap(int recordType){
        this.data = new LinkedHashMap<String, ClusterRecord>();
        this.recordType = recordType;
    }

    /**
     * Creates a new instance of <code>EntityMap</code>
     * @param data
     */
    public EntityMap(Map<String, ClusterRecord> data, int recordType){
        this.data = data;
        this.recordType = recordType;
    }
    
    public Map<String, ClusterRecord> getData() {
        return data;
    }

    public void setData(Map<String, ClusterRecord> data) {
        this.data = data;
    }
    
    /**
     * This method returns the <code>ClusterRecord</code> for the associated
     * OysterID.
     * @param oysterID the index into the EntityMap.
     * @return the ClusterRecord if it exist, otherwise null
     */
    public ClusterRecord getCluster(String oysterID){
        return data.get(oysterID);
    }

    /**
     * Removes the Cluster indexed by the input OysterID from the <code>EntityMap
     * </code>.
     * @param oysterID the index into the EntityMap.
     */
    public void removeCluster(String oysterID) {
        data.remove(oysterID);
    }

    /**
     * Returns the size of the <code>EntityMap</code>.
     * @return the number of clusters.
     */
    public int getSize() {
        int size = -1;
        
        if (data != null) {
            size = data.size();
        }
        
        return size;
    }

    /**
     * The method adds a new entry to the <code>EntityMap</code>.
     * @param cr <code>ClusterRecord</code> to be added.
     */
    public void add(ClusterRecord cr){
        data.put(cr.getOysterID(), cr);
    }
    
    /**
     * This method adds a new identity to the <code>EntityMap</code>.
     * @param oysterID system generated OysterID.
     * @param oir <code>OysterIdentityRecord</code> to be added.
     * @param runID the id for the current resolution run.
     * @param rules the rules that fired for the current oysterID.
     */
    public void addIdentity (String oysterID, OysterIdentityRecord oir, String runID, Set<String> rules, boolean traceOn) {
        ClusterRecord cr = data.get(oysterID);
        
        if (cr == null) {
            cr = new ClusterRecordSet(this.recordType);
        }
        
        if (traceOn){
            // add a self trace to this oir
            TraceRecord tr = new TraceRecord();
//            tr.setOid("*");
            tr.setOid(oysterID);
            tr.setRunID(runID);
            tr.setRule(rules);
            oir.setCurrTrace(tr);
        }
        
        cr.insertRecord(oir);
        cr.setOysterID(oysterID);
        
        add(cr);
    }
    
    /**
     * This method adds a new identity to the <code>EntityMap</code>.
     * @param oysterID system generated OysterID.
     * @param cr <code>ClusterRecord</code> to be added.
     * @param runID the id for the current resolution run. A null runId is used 
     *        to determine that this is an existing cluster being loaded from a 
     *        file.
     * @param rules the rules that fired for the current oysterID.
     */
    public void addIdentity (String oysterID, ClusterRecord cr, String runID, Set<String> rules, boolean traceOn) {
        cr.setOysterID(oysterID);
        
        // add a self trace to this cluster if it is a new cluster
        if (traceOn && runID != null) {
            TraceRecord tr = new TraceRecord();
//            tr.setOid("*");
            tr.setOid(oysterID);
            tr.setRunID(runID);
            tr.setRule(rules);
            cr.getOysterIdentityRecord(0).setCurrTrace(tr);
        }
        add(cr);
    }
    
    /**
     * This method takes the new <code>ClusterRecord</code> and merges it with
     * the old <code>ClusterRecord</code> then replaces the old <code>
     * ClusterRecord</code> in the <code>EntityMap</code> with the merged one. 
     * This allows any new information to be kept with the old.
     * @param oysterID the index into the EntityMap.
     * @param cr <code>ClusterRecord</code> to be updated.
     * @param runID the id for the current resolution run.
     * @param rules the rules that fired for the current oysterID.
     */
    public void updateIdentity (String oysterID, ClusterRecord cr, String runID, Set<String> rules, boolean trace) {
        // get the identity for this index
        ClusterRecord old = data.get(oysterID);
        
        if (old != null && !cr.getOysterID().equals(old.getOysterID())){
            // update any merges
            // FIXME: How should I handle multiple merges, i.e. old has merges and so does cr, so there are now three sets of merges
            Map<String,String> merges = cr.getMerges();
            
            if (merges == null){
                merges = new LinkedHashMap<String,String>();
            }
            
            merges.putAll(old.getMerges());
            merges.put(old.getOysterID(), old.getValuesByAttribute("@RefID"));
            cr.setMerges(merges);
            
            cr.merge(old, runID, rules, trace);
            old = null;
        }
        cr.setOysterID(oysterID);
        add(cr);
    }

    public void clear(){
        this.data.clear();
    }
    
    public void close(){
    }

    public List<String> getKeys(String[] entities) {
        return Arrays.asList(data.keySet().toArray(entities));
    }
}
