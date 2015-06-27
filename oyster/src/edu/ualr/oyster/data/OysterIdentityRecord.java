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

package edu.ualr.oyster.data;

import edu.ualr.oyster.core.ReferenceItem;
import edu.ualr.oyster.kb.TraceRecord;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;

/**
 * The <code>OysterIdentityRecord</code> class is used to hold a single record.
 * 
 * Created on Dec 3, 2010 12:07:30 PM
 * @author Eric D. Nelson
 */
public abstract class OysterIdentityRecord implements Comparable<OysterIdentityRecord>, Cloneable, Serializable {
    private static final long serialVersionUID = -8995282561321391991L;
    
    /** attribute = tag */
    protected static TreeMap <String, String>md1 = new TreeMap<String, String>();
    
    /** tag = attribute */
    protected static TreeMap <String, String>md2 = new TreeMap<String, String>();
    
    protected boolean input = false;
    
    /** OYSTER_Version 3.2 Requirement 3.2.3: Add child element &lt;Trace&gt; in
     * element &lt;Traces&gt;. &lt;Trace&gt; element has three attributes: "OID",
     * "RunID", and "Rule". The value of attribute Rule is the Rule identifier 
     * which brings this reference into the corresponding OYSTER ID (the value 
     * of attribute OID) by the corresponding Run (the value of attribute RunID).
     */
    protected TraceRecord currTrace = null;
    protected Set<TraceRecord> prevTraces = null;
    
    /**
     * Creates a new instance of OysterIdentityRecord
     */
    public OysterIdentityRecord() {
        if (md1.isEmpty()){
            TreeMap<String, String> metadata = ClusterRecord.getMetadata();
            
            for (Iterator<Entry<String, String>> it2 = metadata.entrySet().iterator(); it2.hasNext();){
                Entry<String, String> entry = it2.next();
                
                md1.put(entry.getValue(), entry.getKey());
                md2.put(entry.getKey(), entry.getValue());
            }
        }
        
        prevTraces = new LinkedHashSet<TraceRecord>();
    }

    public boolean isInput() {
        return input;
    }

    public void setInput(boolean input) {
        this.input = input;
    }

    /**
     * Returns the current auditing traces for this <code>ClusterRecord</code>
     * @return the current auditing traces
     */
    public TraceRecord getCurrTrace() {
        return currTrace;
    }

    /**
     * Sets the current auditing traces for this <code>ClusterRecord</code>
     * @param currTrace the current auditing traces to be set
     */
    public void setCurrTrace(TraceRecord currTrace) {
        this.currTrace = currTrace;
    }

    /**
     * Returns the previous auditing traces for this <code>ClusterRecord</code>
     * @return the previous auditing traces
     */
    public Set<TraceRecord> getPrevTraces() {
        return prevTraces;
    }

    /**
     * Sets the previous auditing traces for this <code>ClusterRecord</code>
     * @param prevTraces the previous auditing traces to be set
     */
    public void setPrevTraces(Set<TraceRecord> prevTraces) {
        this.prevTraces = prevTraces;
    }

    /**
     * This method returns a formated string to be used by the logger in place 
     * of the to of the to String method. 
     * @return the String representation of this object.
     */
    public String toExplanationString(){
        StringBuilder sb = new StringBuilder();
        int count = 0;
        
        for(Iterator<String> it = md2.keySet().iterator(); it.hasNext();){
            String tag = it.next();
            String name = md2.get(tag);
            sb.append(name).append("{").append(getValueByTag(tag)).append("}");
            
            if (count < md2.size()-1) {
                sb.append(", ");
            }
            
            count++;
        }
        return sb.toString();
    }

    /**
     * Returns the class metadata (tag / attribute pairs)
     * @return the class metadata
     */
    public TreeMap<String, String> getMetaData() {
        /*
        TreeMap<String, String> metadata = new TreeMap<String, String>();
        
        for (Iterator<String> it = md2.keySet().iterator(); it.hasNext();){
            String key = it.next();
            String value = md2.get(key);
            
            metadata.put(key, value);
        }
         */
        return md2;
    }

    public void updateMetaData(){
        TreeMap<String, String> metadata = ClusterRecord.getMetadata();

        for (Iterator<Entry<String, String>> it2 = metadata.entrySet().iterator(); it2.hasNext();) {
            Entry<String, String> entry = it2.next();

            md1.put(entry.getValue(), entry.getKey());
            md2.put(entry.getKey(), entry.getValue());
        }
    }
    
    /**
     * Returns the Metadata tag for the attribute value.
     * @param attribute the attribute to be looked up
     * @return the metadata tag if it exists, otherwise null
     */
    static String getTagforValue(String attribute){
        return md1.get(attribute);
    }
    
    /**
     * Returns the data.
     * @return the data.
     */
    public abstract Object getData();

    /**
     * Sets the data.
     * @param data the data to be set.
     */
    public abstract void setData(Object data);

    /**
     * This method adds a keyword value pair to the <code>OysterIdentityRecord</code>.
     * @param key the attribute name that is to be used as the key.
     * @param value the data value to be associated with the key.
     */
    public abstract void add(String key, String value) ;

    /**
     * Appends the data value to an existing data value otherwise inserts the
     * value only if the value is not null/empty.
     * @param key the attribute name.
     * @param value value a String of data.
     */
    public abstract void append(String key, String value);
    
    /**
     * Removes all data from this <code>OysterIdentityRecord</code>. 
     */
    public abstract void clear() ;
    
    /**
     * This method preforms a deep copy of the current OysterIdentityRecord.
     * @return a copy of this OysterIdentityRecord.
     */
    @Override
    public OysterIdentityRecord clone() throws CloneNotSupportedException {
        return (OysterIdentityRecord) super.clone();
    }
    
    /**
     * Returns the comparison of the <code>OysterIdentityRecord</code>. If the
     * <code>OysterIdentityRecord</code>s are found to be equal the return value
     * is 0.
     * @param o the <code>OysterIdentityRecord</code> to compare
     * @return 0 if the <code>OysterIdentityRecord</code> are equal otherwise a 
     * negative or non-negative integer
     */
    @Override
    public abstract int compareTo(OysterIdentityRecord o);
    
    /**
     * This method converts an ArrayList of <code>ReferenceItems</code> into a 
     * OysterIdentityRecord.
     * @param referenceItems to be converted.
     */
    public abstract void convertToOIR(ArrayList<ReferenceItem> referenceItems);
    
    /**
     * Returns the data for the Oyster Attribute Item value.
     * @param key the Oyster Attribute Item value.
     * @return the data value that matches the input key, otherwise null.
     */
    public abstract String get(String key) ;

    /**
     * Returns the values of the <code>OysterIdentityRecord</code> as a string.
     * @return the string values of the <code>OysterIdentityRecord</code>
     */
    public abstract String getValues();
    
    /**
     * Returns the data for the CoDoSA tag value.
     * @param tag the CoDoSA tag value.
     * @return a String of data if available, otherwise null.
     */
    public abstract String getValueByTag(String tag);
    
    /**
     * Remove this field from the <code>OysterIdentityRecord</code>
     * @param field
     */
    public abstract void remove(String field);

    /**
     * Checks the equality for the <code>OysterIdentityRecord</code>
     * @param obj the <code>OysterIdentityRecord</code> to check against
     * @return true if the <code>OysterIdentityRecord</code> are equal, otherwise false
     */
    @Override
    public abstract boolean equals(Object obj) ;

    /**
     * Returns the hash code for this <code>OysterIdentityRecord</code>
     * @return the hash code
     */
    @Override
    public abstract int hashCode() ;  
    
    /**
     * Returns the string representation of this <code>OysterIdentityRecord</code>
     * @return the string representation
     */
    @Override
    public abstract String toString();
}
