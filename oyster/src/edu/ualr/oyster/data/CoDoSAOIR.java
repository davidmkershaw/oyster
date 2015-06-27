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
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.TreeMap;

/**
 * The <code>CoDoSAOIR</code> class is used to hold a single record as a 
 * Compressed Document Set Architecture (CoDoSA) string. 
 * 
 * Created on Dec 3, 2010 12:07:30 PM
 * @author Eric D. Nelson
 */
public class CoDoSAOIR extends OysterIdentityRecord implements Comparable<OysterIdentityRecord>{
    private static final long serialVersionUID = 5238709313366540694L;
    
    /** Data as a CoDoSA string */
    private String data = "";
    
    /**
     * Creates a new instance of CoDoSAOIR
     */
    public CoDoSAOIR() {
        super();
    }

    /**
     * Returns the data as a Compressed Document Set Architecture (CoDoSA) string.
     * @return the data as a CoDoSA string.
     */
    @Override
    public String getData() {
        return order();
    }

    /**
     * Sets the CoDoSA data String.
     * @param data the CoDoSA String to be set.
     */
    @Override
    public void setData(Object data) {
        this.data = (String)data;
    }

    /**
     * This method adds a keyword value pair to the <code>CoDoSAOIR</code>.
     * @param key the attribute name that is to be used as the key.
     * @param value the data value to be associated with the key.
     */
    @Override
    public void add(String key, String value) {
        int begin, end;
        String tag = md1.get(key);
        
        if (tag != null) {
            // find the tag if it exists in the data string
            if (!data.equals("")) {
                if ((begin = data.indexOf("[" + tag + "^")) != -1) {
                    end = data.indexOf("]", begin);

                    data = data.substring(0, begin + tag.length() + 2) + value + data.substring(end);
                } else {
                    data = data.trim().substring(0, data.trim().length()) + "[" + tag + "^" + value + "]]";
                }
            } else{
                data = "[[" + tag + "^" + value + "]]";
            }
        }
    }

    /**
     * Returns the data for the Oyster Attribute Item value.
     * @param key the Oyster Attribute Item value.
     * @return the data value that matches the input key, otherwise null.
     */
    @Override
    public String get(String key) {
        String value = null;
        String tag = md1.get(key);
        int begin, end;
        
        if ((begin = data.indexOf("[" + tag)) != -1){
            end = data.indexOf("]", begin);
            value = data.substring(begin+tag.length()+2, end);
        }
        
        return value;
    }

    /**
     * Returns the data for the CoDoSA tag value.
     * @param tag the CoDoSA tag value.
     * @return a String of data if available, otherwise null.
     */
    @Override
    public String getValueByTag(String tag){
        String value = null;
        int begin, end;
        
        if ((begin = data.indexOf("[" + tag)) != -1){
            end = data.indexOf("]", begin);
            value = data.substring(begin+tag.length()+2, end);
        }
        
        return value;
    }
    
    /**
     * Returns the values of the <code>CoDoSAOIR</code> as a string.
     * @return the string values of the <code>CoDoSAOIR</code>
     */
    @Override
    public String getValues() {
        String[] temp = data.split("[\\]\\[]");
        TreeMap<String, String> m = new TreeMap<String, String>();

        for (int i = 1; i < temp.length; i++) {
            if (!temp[i].equals("")) {
                String[] temp2 = temp[i].split("\\^");
                if (temp2.length > 1) {
                    m.put(temp2[0], temp2[1]);
                }
            }
        }
        return m.values().toString();
    }

    /**
     * Appends the data value to an existing data value otherwise inserts the
     * value only if the value is not null/empty.
     * @param key the attribute name.
     * @param value value a String of data.
     */
    @Override
    public void append(String key, String value) {
        int begin, end;

        if (value != null && !value.equals("")) {

            String tag = md1.get(key);
            if (tag != null) {
                // find the tag if it exists
                if ((begin = data.indexOf("[" + tag + "^")) != -1) {
                    end = data.indexOf("]", begin);
                    // does the value already exist?
                    if (!data.substring(begin + 2 + tag.length(), end).equalsIgnoreCase(value)) {
                        data = data.substring(0, end) + "|" + value + data.substring(end);
                    }
                } else {
                    if (!data.trim().equals("")) {
                        data = data.trim().substring(0, data.trim().length() - 1) + "[" + tag + "^" + value + "]]";
                    } else {
                        data = "[[" + tag + "^" + value + "]]";
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
        String tag;
        data = "[";
        for (Iterator<ReferenceItem> it = referenceItems.iterator(); it.hasNext();){
            ReferenceItem ri = it.next();
            
            if (ri.getAttribute() != null){
                tag = md1.get(ri.getAttribute());
                
                if (ri.getData() != null && !ri.getData().trim().equals("") && tag != null){
                    int begin, end;
                    if ((begin = data.indexOf("[" + tag + "^")) != -1) {
                        end = data.indexOf("]", begin);
                        
                        // don't add data that you already have
                        String s = getValueByTag(tag);
                        if (s == null) {
                            s = "";
                        }
                        
                        String[] sArr = s.split("[|]");
                        boolean found = false;
                        for (int i = 0; i < sArr.length; i++) {
                            if (sArr[i].equalsIgnoreCase(ri.getData())) {
                                found = true;
                            }
                        }
                        
                        if (!found){
                            data = data.substring(0, end) + "|" + ri.getData() + data.substring(end);
                        }
                    } else {
                        data += "[" + tag + "^" + ri.getData() + "]";
                    }
                }
            }
        }
        data += "]";
    }
    
    /**
     * Remove this field from the <code>CoDoSAOIR</code>
     * @param field
     */
    @Override
    public void remove(String field){
        String tag = md1.get(field);
        int begin, end;
        
        if ((begin = data.indexOf("[" + tag)) != -1){
            end = data.indexOf("]", begin);
            data = data.substring(begin, end+1);
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
        
        final CoDoSAOIR other = (CoDoSAOIR) obj;
        if (this == null && other != null) {
            return false;
        }
        // FIXME: See the TraceRecord equals method
        if ((this.data == null || !this.data.equalsIgnoreCase(other.data)) && !this.data.equalsIgnoreCase(other.data)) {
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
     * Returns the hash code for this <code>OysterIdentityRecord</code>
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
     * Returns the comparison of the <code>CoDoSAOIR</code>. If the
     * <code>CoDoSAOIR</code>s are found to be equal the return value
     * is 0.
     * @param o the <code>OysterIdentityRecord</code> to compare
     * @return 0 if the <code>OysterIdentityRecord</code> are equal otherwise a 
     * negative or non-negative integer
     */
    @Override
    public int compareTo(OysterIdentityRecord o) {
        return this.toString().compareToIgnoreCase(((CoDoSAOIR)o).toString());
    }
    
    /**
     * This method preforms a deep copy of the current CoDoSAOIR.
     * @return a copy of this OysterIdentityRecord.
     */
    @Override
    public OysterIdentityRecord clone() throws CloneNotSupportedException {
        OysterIdentityRecord oir = super.clone();
        oir.setData(this.data);
        oir.setInput(this.input);
        
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
     * Returns the string representation of this <code>CoDoSAOIR</code>
     * @return the string representation
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(order()).append(", ");
        sb.append("Input record: ").append(this.input).append(", ");
        sb.append("Current Traces: ").append(currTrace);
        sb.append("Previous Traces: ").append(prevTraces);
        return sb.toString();
    }

    /**
     * Removes all data from this <code>CoDoSAOIR</code>. 
     */
    @Override
    public void clear() {
        data = "";
    }
    
    /**
     * This method orders the CoDoSA string alphabetically by tag.
     * @return an ordered CoDoSA string
     */
    private String order() {
        StringBuilder sb = new StringBuilder();
        String [] temp = data.split("[\\]\\[]");
        TreeMap<String, String> m = new TreeMap<String, String>();
        
        for (int i = 1; i < temp.length; i++){
            if (!temp[i].equals("")){
                String [] temp2 = temp[i].split("\\^");
                if (temp2.length > 1) {
                    m.put(temp2[0], temp2[1]);
                } else {
                    m.put(temp2[0], "");
                }
            }
        }
        
        sb.append("[");
        for (Iterator<Entry<String, String>> it = m.entrySet().iterator(); it.hasNext();){
            Entry<String, String> entry = it.next();
            sb.append("[").append(entry.getKey()).append("^").append(entry.getValue()).append("]");
        }
        sb.append("]");
        return sb.toString();
    }
}
