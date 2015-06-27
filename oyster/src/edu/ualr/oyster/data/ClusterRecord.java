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

import edu.ualr.oyster.core.OysterAttribute;
import edu.ualr.oyster.core.OysterAttributes;
import edu.ualr.oyster.kb.TraceRecord;
import java.io.Serializable;
import java.util.Date;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/**
 * <code>ClusterRecord</code> class that is used to hold records that clustered
 * based on the Entity Resolution method that is currently being run. The possible
 * ER approaches are Merge and Clustering.
 *
 * Created on Nov 27, 2010 1:37:04 AM
 * @author Eric D. Nelson
 */
public abstract class ClusterRecord implements Serializable{
    private static final long serialVersionUID = 5002417082195469891L;

    /** The number of records that are contained within this <code>ClusterRecord</code> */
    protected int size = 0;

    /** The Oyster ID for this <code>ClusterRecord</code> */
    protected String oysterID = null;

    /** The CoDoSA style metadata (tag -> attribute) for this <code>ClusterRecord</code> */
    protected static volatile TreeMap<String, String> metadata = null;

    /** */
    // See email Oyster v2.5 Jan 16, 2011
    protected boolean append = false;

    /** The starting CoDoSA tag letter for the metadata for this <code>ClusterRecord</code> */
    protected static String nextTag = "B";

    /** Used to determine persistence for this <code>ClusterRecord</code> */
    protected boolean persistant = false;

    /** Used to determine persistence for this <code>ClusterRecord</code> */
    protected Date creationDate = null;

    /** OYSTER_Version 3.2 Requirement 2.5.4 - 2.5.5 */
    protected Set<String> strToStr = null;
    
    /** OYSTER_Version 3.2 Requirement 2.6.5 - 2.6.9 */
    protected Set<String> negStrToStr = null;
    
    /** This is used in the Change Report it holds the Oyster ID's of the merged clusters */
    protected Map<String,String> merges = null;

    protected static String currentRunID = "0";
    
    /** 
     * This is used to hold the record type that the Cluster record has. This
     * can be -110000 for CoDoSA or -120000 for Map
     */
    protected static int recordType = -1;
    
    /**
     * Creates a new instance of ClusterRecord
     */
    public ClusterRecord(int aRecordType){
        recordType = aRecordType;
        
        merges = new LinkedHashMap<String,String>();
        strToStr = new LinkedHashSet<String>();
        negStrToStr = new LinkedHashSet<String>();
        
        if(metadata == null){
            metadata = new TreeMap<String, String>();
        }
    }

    /**
     * Returns the Attribute Name for the input tag
     * @param tag the input CoDoSA tag
     * @return the Attribute Name associated with the tag, if the does not tag 
     * exists returns null
     */
    public String getAttributeNameByTag(String tag) {
        return metadata.get(tag);
    }

    /**
     * Returns the OysterID for this <code>ClusterRecord</code>
     * @return the OysterID
     */
    public String getOysterID() {
        return oysterID;
    }

    /**
     * Sets the OysterID for this <code>ClusterRecord</code>
     * @param oysterID
     */
    public void setOysterID(String oysterID) {
        this.oysterID = oysterID;
    }

    /**
     * Returns the number of records for this <code>ClusterRecord</code>
     * @return the number of records
     */
    public int getSize() {
        return size;
    }

    /**
     * Returns whether the persistence flag is set for this <code>ClusterRecord</code>
     * @return true if the flag is set, otherwise false.
     */
    public boolean isPersistant() {
        return persistant;
    }

    /**
     * Sets the persistence flag for this <code>ClusterRecord</code>
     * @param persistant
     */
    public void setPersistant(boolean persistant) {
        this.persistant = persistant;
    }

    /**
     * Returns the Creation Date for this <code>ClusterRecord</code>
     * @return the clusters creation date
     */
    public Date getCreationDate() {
        return (Date) creationDate.clone();
    }

    /**
     * Sets the creation date for this <code>ClusterRecord</code>
     * @param creationDate the creation date to be set
     */
    public void setCreationDate(Date creationDate) {
        if (creationDate != null) {
            this.creationDate = new Date(creationDate.getTime());
        }
    }

    /**
     * Returns the asserted structure ids for this <code>ClusterRecord</code>
     * @return the asserted structure information
     */
    public Set<String> getStrToStr() {
        return strToStr;
    }

    /**
     * Sets the asserted structure ids for this <code>ClusterRecord</code>
     * @param strToStr the asserted structure ids to be set
     */
    public void setStrToStr(Set<String> strToStr) {
        this.strToStr = strToStr;
    }

    /**
     * Returns the negative asserted structure ids for this <code>ClusterRecord</code>
     * @return the negative asserted structure information
     */
    public Set<String> getNegStrToStr() {
        return negStrToStr;
    }

    /**
     * Sets the negative asserted structure ids for this <code>ClusterRecord</code>
     * @param negStrToStr the negative asserted structure ids to be set
     */
    public void setNegStrToStr(Set<String> negStrToStr) {
        this.negStrToStr = negStrToStr;
    }
    
    /**
     * Returns the merged cluster ids for this <code>ClusterRecord</code>
     * @return the merged cluster ids
     */
    public Map<String,String> getMerges() {
        return merges;
    }

    /**
     * Sets the merges for this <code>ClusterRecord</code>
     * @param merges the merges to be set
     */
    public void setMerges(Map<String,String> merges) {
            this.merges = merges;
    }

    /**
     * Returns the Record Type for this <code>ClusterRecord</code>
     * @return the clusters record type
     */
    public int getRecordType() {
        return recordType;
    }
    
    /**
     * @return the currentRunID
     */
    public String getCurrentRunID() {
        return currentRunID;
    }

    /**
     * @param aCurrentRunID the currentRunID to set
     */
    public void setCurrentRunID(String aCurrentRunID) {
        currentRunID = aCurrentRunID;
    }
    
    public LinkedHashSet<OysterIdentityRecord> getRecords(boolean rswoosh) {
        return new LinkedHashSet<OysterIdentityRecord>();
    }
    
    /**
     *
     * @param r
     * @return false
     */
    public boolean match(OysterIdentityRecord r){
        return false;
    }

    /**
     * The method merges the input cluster record into this cluster record.
     * @param old the input cluster to be merged
     * @param runID the id for the current resolution run.
     * @param rules the rules that fired for the current oysterID.
     */
    public void merge(ClusterRecord old, String runID, Set<String> rules, boolean traceOn) {
        // update the merges for this oir
        if (old.getOysterID() != null) {
            merges.put(old.getOysterID(), old.getValuesByAttribute("@RefID"));
        }
        
        for (int i = 0; i < old.getSize(); i++){
            OysterIdentityRecord r = old.getOysterIdentityRecord(i);
            
            if (traceOn){
                // update the traces for this oir
                TraceRecord tr = r.getCurrTrace();

                if (tr == null) {
                    tr = new TraceRecord();
                }

                tr.setOid(this.oysterID);
                tr.setRunID(runID);
                tr.setRule(rules);
                r.setCurrTrace(tr);            
            }
            
            insertRecord(r);
        }
    }
    
    /**
     * This method replaces any XML special characters with it's XML entity
     * @param s the input string to be checked
     * @return the string with any XML characters replaced
     */
    protected String replaceXMLEntities(String s){
        String result = s;
        if (result != null && result.length() > 0){
            result = result.replace("&", "&amp;");
            result = result.replace("\"", "&quot;");
            result = result.replace("'", "&apos;");
            result = result.replace("<", "&lt;");
            result = result.replace(">", "&gt;");
        }
        return result;
    }
    
    /**
     * Returns the metadata for this <code>ClusterRecord</code>
     * @return the metadata
     */
    public static TreeMap<String, String> getMetadata() {
        return metadata;
    }

    /**
     * Sets the metadata for this <code>ClusterRecord</code>
     * @param aMetadata
     */
    public void setMetadata(TreeMap<String, String> aMetadata) {
        if (metadata == null) {
            metadata = aMetadata;
        }
    }

    /**
     * Creates the metadata and index based on the <code>OysterAttributes</code>.
     * @param attributes the <code>OysterAttributes</code> used to create the
     * metadata.
     */
    public void createMetaData(OysterAttributes attributes) {
        String alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        int pos = 1, pos2 = -1;

        if (metadata == null) {
            metadata = new TreeMap<String, String>();
        }

        metadata.put("A", "@RefID");

        System.out.println();
        System.out.println("A  @RefID");
        for (Iterator<OysterAttribute> it = attributes.getAttrComp().keySet().iterator(); it.hasNext();) {
            OysterAttribute oa = it.next();

            // get the tag for this data element
            String tag;
            if (pos < alphabet.length()) {
                tag = "" + alphabet.charAt(pos);

                if ((pos + 1) < alphabet.length()) {
                    nextTag = "" + alphabet.charAt(pos + 1);
                } else {
                    nextTag = "" + alphabet.charAt(pos2 + 1) + alphabet.charAt((pos + 1) % 26);
                }
            } else {
                tag = "" + alphabet.charAt(pos2) + alphabet.charAt(pos % 26);

                if ((pos + 1) < alphabet.length()) {
                    nextTag = "" + alphabet.charAt(pos2) + alphabet.charAt((pos % 26) + 1);
                } else {
                    nextTag = "" + alphabet.charAt(pos2) + alphabet.charAt((pos + 1) % 26);
                }
            }

            System.out.println(tag + " " + oa.getName());
            metadata.put(tag, oa.getName());

            pos++;

            if (pos % 26 == 0) {
                pos2++;
            }
        }
    }

    /**
     * This method updates the metadata and index with the new attribute name
     * only if it currently is not in the metadata.
     * @param name the attribute name to be inserting into the metadata.
     */
    public void updateMetaData(String name) {
        String alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        int pos, pos2 = -1;

        System.out.println(nextTag + " " + name);
        metadata.put(nextTag, name);

        // update tag
        if (nextTag.length() == 2) {
            pos2 = alphabet.indexOf(nextTag.charAt(0));
            pos = alphabet.indexOf(nextTag.charAt(1));

            if (pos == 25) {
                pos = 0;
                pos2++;
            } else {
                pos++;
            }
        } else {
            pos = alphabet.indexOf(nextTag.charAt(0));

            if (pos == 25) {
                pos = 0;
                pos2++;
            } else {
                pos++;
            }
        }

        if (pos2 == -1) {
            nextTag = "" + alphabet.charAt(pos);
        } else {
            nextTag = "" + alphabet.charAt(pos2) + alphabet.charAt(pos);
        }
    }

    /**
     * This method add attributes to the metadata starting at the input tag.
     * @param name the attribute name to be updated into the metadata.
     * @param tag the tag to update
     */
    public void updateMetaData(String name, String tag) {
        String alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        int pos, pos2 = -1;

        nextTag = tag;

        System.out.println(nextTag + " " + name);
        metadata.put(nextTag, name);

        // update tag
        if (nextTag.length() == 2) {
            pos2 = alphabet.indexOf(nextTag.charAt(0));
            pos = alphabet.indexOf(nextTag.charAt(1));

            if (pos == 25) {
                pos = 0;
                pos2++;
            } else {
                pos++;
            }
        } else {
            pos = alphabet.indexOf(nextTag.charAt(0));

            if (pos == 25) {
                pos = 0;
                pos2++;
            } else {
                pos++;
            }
        }

        if (pos2 == -1) {
            nextTag = "" + alphabet.charAt(pos);
        } else {
            nextTag = "" + alphabet.charAt(pos2) + alphabet.charAt(pos);
        }
    }

    /**
     * Returns the metadata for this <code>ClusterRecord</code>
     * @return the String representation of the metadata
     */
    public String outputMetaData(){
        StringBuilder sb = new StringBuilder();
        sb.append("Metadata=").append(metadata);
        return sb.toString();
    }

    /**
     * Empties the <code>ClusterRecord</code>
     */
    public abstract void clear();

    /**
     * This method preforms a deep copy of the current ClusterRecord.
     * @return a copy of this ClusterRecord.
     */
    @Override
    public abstract ClusterRecord clone();
    
    /**
     * This method converts the <code>ClusterRecord</code> to an XML representation.
     * @param date the system date to be used as the creation date only if this is
     * a NEW cluster.
     * @return the XML string
     */
    public abstract String convertToXML(String date);

    /**
     * Returns the data for this entire column for this <code>ClusterRecord</code>
     * @param field the attribute name to be looked for
     * @return <code>Vector</code> containing the data for this field
     */
    public abstract Set<String> getField(String field);

    /**
     * This method "collapses" the <code>ClusterRecord</code> to a single record.
     * This is done by merging data within a attribute name's domain.
     * @return a merged record of the <code>ClusterRecord</code>.
     */
    public abstract OysterIdentityRecord getMergedRecord();

    /**
     * This method returns the <code>OysterIdentityRecord</code> at the index position. If the
     * index is larger than the record set null is returned.
     * @param index the position to be looked at
     * @return the <code>OysterIdentityRecord</code> if found, otherwise null.
     */
    public abstract OysterIdentityRecord getOysterIdentityRecord(int index);

    /**
     * Returns the data for this entire column for this <code>ClusterRecord</code>
     * @param field the attribute name to be looked for
     * @return a pipe delimited String containing the data for this field
     */
    public abstract String getValuesByAttribute(String field);

    /**
     * This method inserts the <code>OysterIdentityRecord</code> into the <code>ClusterRecord
     * </code>.
     * @param r the <code>OysterIdentityRecord</code> to be inserted.
     */
    public abstract void insertRecord(OysterIdentityRecord r);
    public abstract void insertRecord(OysterIdentityRecord r, boolean skipCheck);

    /**
     * This method removes the input field from all records in this <code>ClusterRecord</code>
     * @param field the attribute field to remove
     */
    public abstract void removeField(String field);

    /**
     * This method removes the OysterIdentityRecord at this index from this <code>ClusterRecord</code>
     * @param index of the OysterIdentityRecord to remove
     */
    public abstract OysterIdentityRecord remove(int index);
    
    /**
     * The String representation of this <code>ClusterRecord</code>
     * @return String representation
     */
    @Override
    public abstract String toString();
    
    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final ClusterRecord other = (ClusterRecord) obj;
        if (this.size != other.size) {
            return false;
        }
        if ((this.oysterID == null) ? (other.oysterID != null) : !this.oysterID.equals(other.oysterID)) {
            return false;
        }
        if (this.append != other.append) {
            return false;
        }
        if (this.persistant != other.persistant) {
            return false;
        }
        if (this.creationDate != other.creationDate && (this.creationDate == null || !this.creationDate.equals(other.creationDate))) {
            return false;
        }
        if (this.strToStr != other.strToStr && (this.strToStr == null || !this.strToStr.equals(other.strToStr))) {
            return false;
        }
        if (this.negStrToStr != other.negStrToStr && (this.negStrToStr == null || !this.negStrToStr.equals(other.negStrToStr))) {
            return false;
        }
        if (this.merges != other.merges && (this.merges == null || !this.merges.equals(other.merges))) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int hash = 5;
        hash = 59 * hash + this.size;
        hash = 59 * hash + (this.oysterID != null ? this.oysterID.hashCode() : 0);
        hash = 59 * hash + (this.append ? 1 : 0);
        hash = 59 * hash + (this.persistant ? 1 : 0);
        hash = 59 * hash + (this.creationDate != null ? this.creationDate.hashCode() : 0);
        hash = 59 * hash + (this.strToStr != null ? this.strToStr.hashCode() : 0);
        hash = 59 * hash + (this.negStrToStr != null ? this.negStrToStr.hashCode() : 0);
        hash = 59 * hash + (this.merges != null ? this.merges.hashCode() : 0);
        return hash;
    }
    
    public abstract String determineClusterState();
}