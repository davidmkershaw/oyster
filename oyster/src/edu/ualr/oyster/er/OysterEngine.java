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

package edu.ualr.oyster.er;

import edu.ualr.oyster.data.ClusterRecord;
import edu.ualr.oyster.kb.OysterIdentityRepository;
import java.util.logging.FileHandler;
import java.util.logging.Logger;

/**
 * OysterEngine.java
 * Created on Sep 25, 2011 12:12:20 AM
 * @author enelso
 */
public abstract class OysterEngine {
    /** The Repository that are used for this ER engine */
    protected OysterIdentityRepository repository = null;
    
    /** The current cluster record to integrate */
    protected ClusterRecord clusterRecord = null;
    
    /** The name of the current source being integrated */
    protected String currentSourceName = "";
    
    /** */
    protected Logger logger = null;
    
    /** */
    protected FileHandler fileHandler = null;
    
    /** */
    protected int recordType;
    
    /** */
    protected boolean debug = false;
    
    /** The flag used to determine if the source is capturable */
    protected boolean capture = false;
    
    /** The total size of candidate lists from an ER run */
    protected int totalCandidatesDeDupSize = 0;
    
    /** The total size of candidate lists from an ER run */
    protected int totalCandidatesSize = 0;

    /** The total number of Candidates from the ER run */
    protected int totalCandidates = 0;

    /** The number of Records Resolved from the ER run */
    protected int resolvedRecords = 0;

    /** The total number of Candidates that matched an input record for the ER run */
    protected int totalMatchedCount = 0;
    protected long matchingLatency = 0;
    protected long maxMatchingLatency = 0;
    protected long minMatchingLatency = Long.MAX_VALUE;
    protected long nonMatchingLatency = 0;
    protected long maxNonMatchingLatency = 0;
    protected long minNonMatchingLatency = Long.MAX_VALUE;
    
    /**
     * Creates a new instance of OysterEngine
     */
    public OysterEngine(){
    }
    
    /**
     * Returns the <code>OysterIdentityRepository</code> for this engine.
     * @return the <code>OysterIdentityRepository</code>.
     */
    public OysterIdentityRepository getRepository () {
        return repository;
    }

    /**
     * Sets the <code>OysterIdentityRepository</code> for this engine.
     * @param repository the <code>OysterIdentityRepository</code>.
     */
    public void setRepository (OysterIdentityRepository repository) {
        this.repository = repository;
    }

    /**
     * Returns the current <code>ClusterRecord</code>.
     * @return a <code>ClusterRecord</code>.
     */
    public ClusterRecord getClusterRecord () {
        return clusterRecord;
    }

    /**
     * Sets the engines list of <code>ClusterRecord</code>.
     * @param clusterRecord the <code>ClusterRecord</code> of items to be integrated.
     */
    public void setClusterRecord (ClusterRecord clusterRecord) {
        this.clusterRecord = clusterRecord;
    }
    
    /**
     * Returns the current SourceName for the source being integrated by the engine.
     * @return currentSourceName
     */
    public String getCurrentSourceName() {
        return currentSourceName;
    }

    /**
     * Sets the current SourceName for the source being integrated by the engine.
     * @param currentSourceName the source name to be set.
     */
    public void setCurrentSourceName(String currentSourceName) {
        this.currentSourceName = currentSourceName;
    }
    
    /**
     * Returns whether the engine is in debug mode.
     * @return true if the engine is in debug mode, otherwise false.
     */
    public boolean isDebug () {
        return debug;
    }

    /**
     * Enables/disables debug mode for the engine.
     * @param debug true to enable debug mode, false to disable it.
     */
    public void setDebug (boolean debug) {
        this.debug = debug;
    }

    /**
     * Returns whether the engine is in capture mode.
     * @return true if the engine is in capture mode, otherwise false.
     */
    public boolean isCapture() {
        return capture;
    }

    /**
     * Enables/disables capture mode for the engine.
     * @param capture true to enable capture mode, false to disable it.
     */
    public void setCapture(boolean capture) {
        this.capture = capture;
    }

    /**
     * Returns the unique current total candidate list size
     * @return the total candidate list size
     */
    public int getTotalCandidatesDeDupSize() {
        return totalCandidatesDeDupSize;
    }

    /**
     * Returns the current total candidate list size
     * @return the total candidate list size
     */
    public int getTotalCandidatesSize() {
        return totalCandidatesSize;
    }

    /**
     * Returns the current total number of candidates
     * @return the total candidate number
     */
    public int getTotalCandidates() {
        return totalCandidates;
    }

    /**
     * Returns the current total number of matched candidates
     * @return the total matched candidates
     */
    public int getTotalMatchedCount() {
        return totalMatchedCount;
    }

    public int getResolvedRecords() {
        return resolvedRecords;
    }

    public long getMatchingLatency() {
        return matchingLatency;
    }

    public void setMatchingLatency(long matchingLatency) {
        this.matchingLatency = matchingLatency;
    }

    public long getMaxMatchingLatency() {
        return maxMatchingLatency;
    }

    public void setMaxMatchingLatency(long maxMatchingLatency) {
        this.maxMatchingLatency = maxMatchingLatency;
    }

    public long getMinMatchingLatency() {
        return minMatchingLatency;
    }

    public void setMinMatchingLatency(long minMatchingLatency) {
        this.minMatchingLatency = minMatchingLatency;
    }

    public long getNonMatchingLatency() {
        return nonMatchingLatency;
    }

    public void setNonMatchingLatency(long nonMatchingLatency) {
        this.nonMatchingLatency = nonMatchingLatency;
    }

    public long getMaxNonMatchingLatency() {
        return maxNonMatchingLatency;
    }

    public void setMaxNonMatchingLatency(long maxNonMatchingLatency) {
        this.maxNonMatchingLatency = maxNonMatchingLatency;
    }

    public long getMinNonMatchingLatency() {
        return minNonMatchingLatency;
    }

    public void setMinNonMatchingLatency(long minNonMatchingLatency) {
        this.minNonMatchingLatency = minNonMatchingLatency;
    }
}
