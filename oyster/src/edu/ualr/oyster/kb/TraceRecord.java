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

import java.io.Serializable;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * TraceRecord.java
 * Created on Nov 20, 2011 8:14:08 PM
 * @author Eric D. Nelson
 */
public class TraceRecord implements Comparable, Cloneable, Serializable {
    /** The Oyster ID */
    private String oid = null;

    /** The sequential number assigned for each run */
    private String runID = "";
    
    /** The rule(s) that was fired for this record */
    private Set<String> rule = null;
    
    /**
     * Creates a new instance of TraceRecord
     */
    public TraceRecord(){
        rule = new LinkedHashSet<String>();
    }

    /**
     * Returns the Oyster ID for this <code>TraceRecord</code>.
     * @return oid 
     */
    public String getOid() {
        return oid;
    }

    /**
     * Sets the Oyster ID for this <code>TraceRecord</code>.
     * @param oid
     */
    public void setOid(String oid) {
        this.oid = oid;
    }

    /**
     * Returns the Run ID for this <code>TraceRecord</code>.
     * @return runID
     */
    public String getRunID() {
        return runID;
    }

    /**
     * Sets the Run ID for this <code>TraceRecord</code>.
     * @param runID
     */
    public void setRunID(String runID) {
        this.runID = runID;
    }

    /**
     * Returns the rule for this <code>TraceRecord</code>.
     * @return rule
     */
    public Set<String> getRule() {
        return rule;
    }

    /**
     * Sets the rule for this <code>TraceRecord</code>.
     * @param rule
     */
    public void setRule(Set<String> rule) {
        this.rule = rule;
    }
    
    /**
     * This method preforms a deep copy of the current TraceRecord.
     * @return a copy of this TraceRecord.
     */
    @Override
    public TraceRecord clone() throws CloneNotSupportedException {
        TraceRecord tr = (TraceRecord) super.clone();
        tr.setOid(oid);
        tr.setRunID(runID);
        tr.getRule().addAll(rule);
        return tr;
    }

    @Override
    public int compareTo(Object o) throws ClassCastException {
        if (!(o instanceof TraceRecord)) {
            throw new ClassCastException("Expected a TraceRecord Object.");
        }
        
        String anotherTrace = ((TraceRecord) o).toString();
        return this.toString().compareToIgnoreCase(anotherTrace);
    }

    @Override
    public boolean equals(Object obj) {
        boolean flag = true;
        if (obj == null) {
            flag = false;
        } else {
            if (getClass() != obj.getClass()) {
                flag = false;
            } else {
                final TraceRecord other = (TraceRecord) obj;
                if (other == null) {
                    flag = false;
                } else {
                    if (this.oid != null && other.oid != null && !this.oid.equalsIgnoreCase(other.oid)) {
                        flag = false;
                    }

                    if (this.runID != null && other.runID != null && !this.runID.equalsIgnoreCase(other.runID)) {
                        flag = false;
                    }

                    if (this.rule != null && other.rule != null && !this.rule.equals(other.rule)) {
                        flag = false;
                    }
                }
            }
        }
        return flag;
    }

    @Override
    public int hashCode() {
        int hash = 3;
        hash = 53 * hash + (this.oid != null ? this.oid.hashCode() : 0);
        hash = 53 * hash + (this.runID != null ? this.runID.hashCode() : 0);
        hash = 53 * hash + (this.rule != null ? this.rule.hashCode() : 0);
        return hash;
    }
    
    /**
     * 
     * @return String
     */
    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();
        sb.append("OID: ").append(oid).append(", ");
        sb.append("RunID: ").append(runID).append(", ");
        sb.append("Rule: ").append(rule);
        return sb.toString();
    }
}
