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

package edu.ualr.oyster.data;

import edu.ualr.oyster.core.ReferenceItem;
import edu.ualr.oyster.kb.TraceRecord;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;
import java.util.TreeMap;

/**
 * The <code>OysterIdentityRecordMap</code> class is used to hold a single  
 * record as a keyword value pair of the attribute name to data item.
 * 
 * Created on Dec 3, 2011 12:07:30 PM
 * @author Eric D. Nelson
 */
public class OysterIdentityRecordMap extends OysterIdentityRecord implements Comparable<OysterIdentityRecord>, Serializable{
    private static final long serialVersionUID = 400275804968230804L;
    
    /** Data as a keyword value pair. The key is the tag letter and the value is
        the data value */
    private Map<String, String> data = null;

    /**
     * Creates a new instance of OysterIdentityRecordMap
     */
    public OysterIdentityRecordMap() {
        super();
        data = new TreeMap<String, String>();
    }

    /**
     * Returns the record data as a <code>TreeMap</code> object.
     * @return the data record.
     */
    @Override
    public Map<String, String> getData() {
        return data;
    }

    /**
     * Sets the data record in a <code>TreeMap</code> object.
     * @param data the record to be set.
     */
    @Override
    @SuppressWarnings( "unchecked" )
    public void setData(Object data) {
        if (data instanceof String){
            // is this a CoDoSA record?
            if (((String)data).startsWith("[[A")){
                throw new UnsupportedOperationException("Not coded for CoDoSA String: " + data);
            } else {
                // {@RefID=Test10e.413202, StudentDateOfBirth=8/11/1999}
                String temp = (String)data;
                if (temp.startsWith("{")){
                    temp = temp.substring(1);
                }
                
                if (temp.endsWith("}")){
                    temp = temp.substring(0, temp.length()-1);
                }
                
                String [] arr = temp.split("[,]");
                
                for (int i = 0; i < arr.length; i++){
                    String [] arr2 = arr[i].split("[=]");
                    
                    String tag = md1.get(arr2[0].trim());
                    
                    if (tag != null){
                        if (arr2.length > 1) {
                            this.data.put(arr2[0].trim(), arr2[1].trim());
                        }
/*                        else {
                            System.out.println("##Error: java.lang.ArrayIndexOutOfBoundsException: 1 ");
                            System.out.println(temp);
                            System.out.println(arr[i]);
                            System.out.println();
                        } */
                    }
                }
            }
        } else {
            this.data = (Map<String, String>)data;
        }
    }

    /**
     * This method adds a keyword value pair to the <code>OysterIdentityRecordMap</code>.
     * @param attribute the attribute name that is to be used as the key.
     * @param data the data value to be associated with the key.
     */
    @Override
    public void add(String attribute, String data) {
        this.data.put(md1.get(attribute), data);
    }

    /**
     * This method returns the data value associated with the key.
     * @param attribute the Oyster Attribute Item value.
     * @return the data value that matches the input key, otherwise null.
     */
    @Override
    public String get(String attribute) {
        String token = null;
        String tag = md1.get(attribute);
        if (tag != null) {
            token = data.get(tag);
        }
        return token;
    }

    /**
     * Returns the data for the Metadata tag value.
     * @param tag the Metadata tag value.
     * @return a String of data if available, otherwise null.
     */
    @Override
    public String getValueByTag(String tag){
/*
        String value = null;
        
        String attribute = md2.get(tag);
        if (attribute != null){
            value = data.get(attribute);
        }
        
        return value;
*/
        return data.get(tag);
    }
    
    /**
     * Returns the values of the <code>OysterIdentityRecordMap</code> as a string.
     * @return the string values of the <code>OysterIdentityRecordMap</code>
     */
    @Override
    public String getValues() {
        return data.values().toString();
    }

    /**
     * Appends the data value to an existing data value otherwise inserts the
     * value only if the value is not null/empty.
     * @param attribute the attribute name.
     * @param value value a String of data.
     */
    @Override
    public void append(String attribute, String value) {
        if (value != null && !value.equals("")) {
            if (attribute != null) {
                // find the key if it exists but the data doesn't
                String tag = md1.get(attribute);
                
                if (tag != null){
                    if (data.containsKey(tag) && !data.containsValue(value)) {
                        String token = data.get(md1.get(attribute));
                        token += "|" + value;
                        data.put(md1.get(attribute), token);
                    } else {
                        data.put(md1.get(attribute), value);
                    }
                }
            }
        }
    }

    /**
     * This method converts an ArrayList of <code>ReferenceItems</code> into a 
     * OysterIdentityRecord.
     * @param referenceItems to be converted.
     */
    @Override
    public void convertToOIR(ArrayList<ReferenceItem> referenceItems){
        for (Iterator<ReferenceItem> it = referenceItems.iterator(); it.hasNext();){
            ReferenceItem ri = it.next();
            
            if (ri.getAttribute() != null && !ri.getAttribute().equalsIgnoreCase("@Skip")){
                if (ri.getData() != null && !ri.getData().trim().equals("")){
                    String tag = md1.get(ri.getAttribute());
                    
                    if (tag != null) {
                        data.put(tag, ri.getData());
                    }
                }
            }
        }
    }

    /**
     * Remove this field from the <code>OysterIdentityRecordMap</code>
     * @param field
     */
    @Override
    public void remove(String field) {
        String tag = md1.get(field);
        if (tag != null) {
            data.remove(tag);
        }
    }

    /**
     * Checks the equality for the <code>OysterIdentityRecord</code>
     * @param obj the <code>OysterIdentityRecord</code> to check against
     * @return true if the <code>OysterIdentityRecord</code> are equal, otherwise false
     */
    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        
        if (getClass() != obj.getClass()) {
            return false;
        }
        
        final OysterIdentityRecordMap other = (OysterIdentityRecordMap) obj;
        if (this == null && other != null) {
            return false;
        }
        //FIXME: See TraceRecord
        if ((this.data == null || !this.data.equals(other.data)) && this.data != other.data) {
            return false;
        }
        
        if ((this.currTrace == null || !this.currTrace.equals(other.currTrace)) && this.currTrace != other.currTrace) {
            return false;
        }
        
        if ((this.prevTraces == null || !this.prevTraces.equals(other.prevTraces)) && this.prevTraces != other.prevTraces) {
            return false;
        }
        
        return true;
    }

    /**
     * Returns the hash code for this <code>OysterIdentityRecordMap</code>
     * @return the hash code
     */
    @Override
    public int hashCode() {
        int hash = 7;
        hash = 79 * hash + (this.data != null ? this.data.hashCode() : 0);
        hash = 79 * hash + (this.currTrace != null ? this.currTrace.hashCode() : 0);
        hash = 79 * hash + (this.prevTraces != null ? this.prevTraces.hashCode() : 0);
        hash = 79 * hash + (this.input ? 1 : 0);
        return hash;
    }

    /**
     * Returns the comparison of the <code>OysterIdentityRecordMap</code>. If the
     * <code>OysterIdentityRecordMaps</code> are found to be equal the return value
     * is 0.
     * @param o the <code>OysterIdentityRecord</code> to compare
     * @return 0 if the <code>OysterIdentityRecord</code> are equal otherwise a 
     * negative or non-negative int
     */
    @Override
    public int compareTo(OysterIdentityRecord o) {
        return this.toString().compareToIgnoreCase(((OysterIdentityRecordMap)o).toString());
    }
    
    /**
     * This method preforms a deep copy of the current OysterIdentityRecordMap.
     * @return a copy of this OysterIdentityRecord.
     */
    @Override
    public OysterIdentityRecord clone()throws CloneNotSupportedException {
        OysterIdentityRecord oir = super.clone();
        
        oir.setInput(this.input);

        // do a deep copy
        Map<String, String> m = new TreeMap<String, String>();
        m.putAll(this.data);
        oir.setData(m);

        oir.currTrace = this.currTrace;
        
        // do a deep copy on the previous traces
        if (!this.prevTraces.isEmpty()){
            for (Iterator<TraceRecord> it = this.prevTraces.iterator(); it.hasNext();) {
                TraceRecord tr = it.next();
                oir.getPrevTraces().add(tr);
            }
        }
        
        return oir;
    }

    /**
     * Returns the string representation of this <code>OysterIdentityRecordMap</code>
     * @return the string representation
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (Iterator<String> it = data.keySet().iterator(); it.hasNext();) {
            String key = it.next();
            String value = data.get(key);
            sb.append(md2.get(key)).append("=").append(value).append(", ");
        }
        sb.append("Input record: ").append(this.input).append(", ");
        sb.append("Current Traces: ").append(currTrace).append(", ");
        sb.append("Previous Traces: ").append(prevTraces);
        return sb.toString();
    }
    
    /**
     * This method returns a formated string to be used by the logger in place 
     * of the to of the to String method. 
     * @return the String representation of this object.
     */
    @Override
    public String toExplanationString(){
        StringBuilder sb = new StringBuilder();
        int count = 0;
        
        for(Iterator<String> it = data.keySet().iterator(); it.hasNext();){
            String key = it.next();
            String value = data.get(key);
            sb.append(md2.get(key)).append("{").append(value).append("}");
            
            if (count < data.size()-1) {
                sb.append(", ");
            }
            
            count++;
        }
        return sb.toString();
    }

    /**
     * Removes all data from this <code>OysterIdentityRecordMap</code>. 
     */
    @Override
    public void clear() {
        data.clear();
    }
}
