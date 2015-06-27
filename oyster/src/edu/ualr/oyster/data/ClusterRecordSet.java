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

import edu.ualr.oyster.kb.TraceRecord;
import java.io.Serializable;
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TimeZone;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * <code>ClusterRecordSet</code> class that is used to hold records that clustered
 * based on the Entity Resolution method that is currently being run. The possible
 * ER approaches are Merge and Clustering.
 *
 * Created on Nov 27, 2010 1:37:04 AM
 * @author Eric D. Nelson
 */
public class ClusterRecordSet extends ClusterRecord implements Comparable<ClusterRecord>, Cloneable, Serializable {
    private static final long serialVersionUID = -5763163285639617779L;

    /** The actual records for this <code>ClusterRecord</code> */
    private LinkedHashSet<OysterIdentityRecord> records = null;

    /**
     * Creates a new instance of ClusterRecordSet
     */
    public ClusterRecordSet(int recordType){
        super(recordType);
        records = new LinkedHashSet<OysterIdentityRecord>();
    }

    /**
     * @return the records
     */
    @Override
    public LinkedHashSet<OysterIdentityRecord> getRecords(boolean rswoosh) {
        LinkedHashSet<OysterIdentityRecord> set = new LinkedHashSet<OysterIdentityRecord>();
        if (rswoosh){
            set.add(this.getMergedRecord());
        } else {
            set.addAll(records);
        }
        return set;
    }

    /**
     * This method removes the input field from all records in this <code>ClusterRecord</code>
     * @param field the attribute field to remove
     */
    @Override
    public void removeField(String field) {
        LinkedHashSet<OysterIdentityRecord> s = new LinkedHashSet<OysterIdentityRecord>();
        for (Iterator<OysterIdentityRecord> it = records.iterator(); it.hasNext();){
            OysterIdentityRecord oir = it.next();
            it.remove();

            oir.remove(field);
            s.add(oir);
        }
        records.addAll(s);
    }

    /**
     * Returns the data for this entire column for this <code>ClusterRecord</code>
     * @param field the attribute name to be looked for
     * @return <code>Vector</code> containing the data for this field
     */
    @Override
    public Set<String> getField(String field){
        Set<String> s = new HashSet<String>();

        for (Iterator<OysterIdentityRecord> it = records.iterator(); it.hasNext();){
            OysterIdentityRecord oir = it.next();
            String token = oir.get(field);
            s.add(token);
        }

        return s;
    }

    /**
     * Returns the data for this entire column for this <code>ClusterRecord</code>
     * @param field the attribute name to be looked for
     * @return a pipe delimited String containing the data for this field
     */
    @Override
    public String getValuesByAttribute(String field) {
        StringBuilder result = new StringBuilder(100);
        Set<String> s = new LinkedHashSet<String>();
        for (Iterator<OysterIdentityRecord> it = records.iterator(); it.hasNext();){
            OysterIdentityRecord r = it.next();

            String data = r.get(field);

            if (data != null){
                s.add(data);
            }
        }

        for (Iterator<String> it = s.iterator(); it.hasNext();){
            result.append(it.next()).append("|");
        }

        if (result.toString().endsWith("|")) {
            result = result.delete(result.length()-1, result.length());
        }

        return result.toString().trim();
    }

    /**
     * This method inserts the <code>OysterIdentityRecord</code> into the <code>ClusterRecord
     * </code>.
     * @param r the <code>OysterIdentityRecord</code> to be inserted.
     */
    @Override
    public void insertRecord(OysterIdentityRecord r) {
        insertRecord(r, false);
    }
    
    @Override
    public void insertRecord(OysterIdentityRecord r, boolean skipCheck){
        try {
            OysterIdentityRecord oir = r.clone();

            if (!records.contains(oir)) {
                // be sure there isn't a lesser partial oyster record
                for (Iterator<OysterIdentityRecord> it = records.iterator(); it.hasNext();) {
                    OysterIdentityRecord oir2 = it.next();

                    TraceRecord tr = null;
                    if (oir2.get("@RefID").equals(oir.get("@RefID")) && !skipCheck){
                        // if the trace isn't set set it
                        if (oir2.currTrace == null) {
                            tr = oir.getCurrTrace();
                        }
                        it.remove();
                        size--;

                        if (oir.compareTo(oir2) > 0) {
                            oir = oir2;
                        }

                        if (tr != null && oir.getCurrTrace() == null) {
                            oir.setCurrTrace(tr);
                        }
                    }
                }

                // insert the record
                records.add(oir);
                size++;
            }
        } catch (CloneNotSupportedException ex) {
            Logger.getLogger(ClusterRecordSet.class.getName()).log(Level.SEVERE, null, ex);
        }
    }

    /**
     * This method returns the <code>OysterIdentityRecord</code> at the index position. If the
     * index is larger than the record set null is returned.
     * @param index the position to be looked at
     * @return the <code>OysterIdentityRecord</code> if found, otherwise null.
     */
    @Override
    public OysterIdentityRecord getOysterIdentityRecord(int index){
        OysterIdentityRecord r = null;
        OysterIdentityRecord [] arr = new OysterIdentityRecord[size];

        if (index < size && index >= 0){
            // get record
            r = records.toArray(arr)[index];
        }
        return r;
    }

    /**
     * This method removes the OysterIdentityRecord at this index from this <code>ClusterRecord</code>
     * @param index of the OysterIdentityRecord to remove
     */
    @Override
    public OysterIdentityRecord remove(int index){
        OysterIdentityRecord r = null;
        OysterIdentityRecord [] arr = new OysterIdentityRecord[size];
        LinkedHashSet<OysterIdentityRecord> temp = new LinkedHashSet<OysterIdentityRecord>();

        if (index < size && index >= 0){
            // get record
            r = records.toArray(arr)[index];
            // remove method is not working must be in how I've implemented the OIR
            // flag = records.remove(r);
            
            for (Iterator<OysterIdentityRecord>it = records.iterator(); it.hasNext();){
                OysterIdentityRecord oir = it.next();
                
                if (!oir.get("@RefID").equals(r.get("@RefID"))){
                    temp.add(oir);
                }
            }
            records.clear();
            records.addAll(temp);
            size = records.size();
        }
        return r;
    }
    
    /**
     * This method "collapses" the <code>ClusterRecord</code> to a single record.
     * This is done by merging data within a attribute name's domain.
     * @return a merged record of the <code>ClusterRecord</code>.
     */
    @Override
    public OysterIdentityRecord getMergedRecord(){
        OysterIdentityRecord r;

        switch (recordType){
            case RecordTypes.CODOSA:
                r = new CoDoSAOIR();
                break;
            case RecordTypes.MAP:
                r = new OysterIdentityRecordMap();
                break;
            default: r = new OysterIdentityRecordMap();
        }
        // then get record data
        for (Iterator<OysterIdentityRecord> it = records.iterator(); it.hasNext();){
            OysterIdentityRecord r1 = it.next();

            for (Iterator<String> it2 = metadata.keySet().iterator(); it2.hasNext();){
                String tag = it2.next();
                String attributeName = metadata.get(tag);

                if (!attributeName.equals("@OysterID")){
                    String data = r1.get(attributeName);

                    r.append(attributeName, data);
                }
            }
        }

        if (this.oysterID != null && !this.oysterID.equals("")) {
            r.append("@OysterID", this.oysterID);
        }
        return r;
    }

    /**
     * The String representation of this <code>ClusterRecord</code>
     * @return String representation
     */
    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();
        sb.append("OysterID: ").append(oysterID);
        sb.append(System.getProperty("line.separator"));
        sb.append("Creation Date: ").append(creationDate);
        sb.append(System.getProperty("line.separator"));
        sb.append("Size: ").append(size);
        sb.append(System.getProperty("line.separator"));
        sb.append("Persistant: ").append(persistant);
        sb.append(System.getProperty("line.separator"));

        int i = 0;
        for (Iterator<OysterIdentityRecord> it = records.iterator(); it.hasNext();){
            OysterIdentityRecord oir = it.next();
            sb.append("Record ").append(i++).append(": ").append(oir.toString());
            sb.append(System.getProperty("line.separator"));
        }

        sb.append("Merges: ").append(merges);
        sb.append(System.getProperty("line.separator"));
        sb.append("StrToStr: ").append(strToStr);
        sb.append(System.getProperty("line.separator"));
        sb.append("NegStrToStr: ").append(negStrToStr);
        sb.append(System.getProperty("line.separator"));
        
        return sb.toString();
    }

    /**
     * This method converts the <code>ClusterRecord</code> to an XML representation.
     * @param date the system date to be used as the creation date only if this is
     * a NEW cluster.
     * @return the XML string
     */
    @Override
    public String convertToXML(String date){
        // TODO: Change String Operation to an XML Encoding Operation http://www.odi.ch/prog/design/newbies.php#6
        StringBuffer buf = new StringBuffer();
        buf.append("\t<Identity Identifier=\"").append(oysterID).append("\" CDate=\"");

        // handle the creation date
        if (creationDate == null) {
            buf.append(date);
        } else {
            String DATE_FORMAT = "yyyy-MM-dd";
            SimpleDateFormat sdf = new java.text.SimpleDateFormat(DATE_FORMAT);
            sdf.setTimeZone(TimeZone.getDefault());

            buf.append(sdf.format(creationDate));
        }
        buf.append("\">").append(System.getProperty("line.separator"));

        if (this.strToStr.size() > 0){
            buf.append("\t\t<StrToStr>").append(System.getProperty("line.separator"));
            for (Iterator<String> it = this.strToStr.iterator(); it.hasNext();){
                buf.append("\t\t\t<OID>").append(it.next()).append("</OID>").append(System.getProperty("line.separator"));
            }
            buf.append("\t\t</StrToStr>").append(System.getProperty("line.separator"));
        }
        
        if (this.negStrToStr.size() > 0){
            buf.append("\t\t<NegStrToStr>").append(System.getProperty("line.separator"));
            for (Iterator<String> it = this.negStrToStr.iterator(); it.hasNext();){
                buf.append("\t\t\t<OID>").append(it.next()).append("</OID>").append(System.getProperty("line.separator"));
            }
            buf.append("\t\t</NegStrToStr>").append(System.getProperty("line.separator"));
        }

        buf.append("\t\t<References>").append(System.getProperty("line.separator"));

        OysterIdentityRecord [] a = new OysterIdentityRecord[records.size()];
        List<OysterIdentityRecord> refs = Arrays.asList(records.toArray(a));
        Collections.sort(refs);
        for (Iterator<OysterIdentityRecord> it = refs.iterator(); it.hasNext();){
            OysterIdentityRecord oir = it.next();
            buf.append("\t\t\t<Reference>").append(System.getProperty("line.separator"));
            buf.append("\t\t\t\t<Value>");

            for (Iterator<String>it2 = metadata.keySet().iterator(); it2.hasNext();){
                String tag = it2.next();
                String name = metadata.get(tag);
                if (!name.startsWith("@") || name.equals("@RefID")) {
                    String s = oir.get(name);

                    // get the data replace any XML Entities
                    if (s != null) {
                        buf.append(tag).append("^");
                        s = replaceXMLEntities(s);

                        if (metadata.lastKey().equals(tag)) {
                            buf.append(s);
                        } else {
                            buf.append(s).append("|");
                        }
                    }
                }
            }
            
            // check to be sure that the last char is not a pipe (|)
            if (buf.toString().endsWith("|")){
                buf = buf.replace(buf.length()-1, buf.length(), "");
            }
            buf.append("</Value>").append(System.getProperty("line.separator"));
            
            if ((oir.getPrevTraces() == null || oir.getPrevTraces().isEmpty()) && oir.getCurrTrace() == null){
                buf.append("\t\t\t\t<Traces/>").append(System.getProperty("line.separator"));
            } else {
                TraceRecord tr;
                buf.append("\t\t\t\t<Traces>").append(System.getProperty("line.separator"));
                
                for (Iterator<TraceRecord> it2 = oir.getPrevTraces().iterator(); it2.hasNext();) {
                    tr = it2.next();
                    buf.append("\t\t\t\t\t<Trace OID=\"").append(tr.getOid());
                    buf.append("\" RunID=\"").append(tr.getRunID());
                    buf.append("\" Rule=\"").append(tr.getRule());
                    buf.append("\"/>").append(System.getProperty("line.separator"));
                }

                tr = oir.getCurrTrace();
                if (tr != null){
                    buf.append("\t\t\t\t\t<Trace OID=\"").append(tr.getOid());
                    buf.append("\" RunID=\"").append(tr.getRunID());
                    buf.append("\" Rule=\"").append(tr.getRule());
                    buf.append("\"/>").append(System.getProperty("line.separator"));
                }
                
                buf.append("\t\t\t\t</Traces>").append(System.getProperty("line.separator"));
            }
            buf.append("\t\t\t</Reference>").append(System.getProperty("line.separator"));
        }
        buf.append("\t\t</References>").append(System.getProperty("line.separator"));
        
        buf.append("\t</Identity>");

        return buf.toString();
    }

    /**
     * Returns the comparison of the <code>ClusterRecordSet</code>. If the
     * <code>ClusterRecordSet</code>s are found to be equal the return value
     * is 0.
     * @param o the <code>ClusterRecord</code> to compare
     * @return 0 if the <code>ClusterRecordSet</code> are equal otherwise a 
     * negative or non-negative integer
     */
    @Override
    public int compareTo(ClusterRecord o) {
        return this.toString().compareToIgnoreCase(((ClusterRecordSet)o).toString());
    }

    @Override
    public int hashCode() {
        int hash = 3;
        hash = 31 * hash + this.size;
        hash = 31 * hash + (this.oysterID != null ? this.oysterID.hashCode() : 0);
        hash = 31 * hash + (this.append ? 1 : 0);
        hash = 31 * hash + (this.persistant ? 1 : 0);
        hash = 31 * hash + (this.creationDate != null ? this.creationDate.hashCode() : 0);
        hash = 31 * hash + (this.strToStr != null ? this.strToStr.hashCode() : 0);
        hash = 31 * hash + (this.negStrToStr != null ? this.negStrToStr.hashCode() : 0);
        hash = 31 * hash + (this.merges != null ? this.merges.hashCode() : 0);
        hash = 31 * hash + (this.records != null ? this.records.hashCode() : 0);
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final ClusterRecordSet other = (ClusterRecordSet) obj;
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
        if (this.records != other.records && (this.records == null || !this.records.equals(other.records))) {
            return false;
        }
        return true;
    }
    
    /**
     * This method preforms a deep copy of the current ClusterRecord.
     * @return a copy of this ClusterRecord.
     */
    @Override
    public ClusterRecord clone(){
        ClusterRecord cr = new ClusterRecordSet(recordType);
        for (Iterator<OysterIdentityRecord> it = records.iterator(); it.hasNext();){
            OysterIdentityRecord oir = it.next();
            cr.insertRecord(oir, false);
        }
        
        cr.setOysterID(this.oysterID);
        cr.setCreationDate(this.creationDate);
        cr.setPersistant(persistant);
        
        // this should be a deep copy. If not will need to iterate over each collection
        cr.getMerges().putAll(merges);
        cr.getNegStrToStr().addAll(negStrToStr);
        cr.getStrToStr().addAll(strToStr);
        
        return cr;
    }

    /**
     * Empties the <code>ClusterRecord</code>
     */
    @Override
    public void clear(){
        size = 0;
        oysterID = null;
        records.clear();
    }
    
    /** 
     * The cluster type is used to determine the current state of a cluster as
     * it goes through the ER process.<br>
     * new + new = new<br>
     * new + existing(U|M|X) = update<br>
     * update + existing(U|M|X) = merge<br>
     * existing + existing = merge
     * 
     * <ul>
     * <li>N - New</li>
     * <li>U - Updated</li>
     * <li>M - Merged</li>
     * <li>X - Existing</li>
     * </ul>
     */
    @Override
    public String determineClusterState() {
        String result = "";
        // New Cluster - if there are no previous RunID's, only the current RunID can be found in a cluster
        // Updated - a cluster is updated if it has multiple RunID's but they don't occur in the same reference
        // Merged - If a cluster has current and previous RunID's within a reference
        for (int i = 0; i < this.size; i++){
            OysterIdentityRecord oir = this.getOysterIdentityRecord(i);
            
            if (oir.currTrace == null) {
                if (result.isEmpty()) {
                    // No Change - if there is no current RunID
                    result = "X";
                }
            } else {
//                System.out.println("Current Trace:" + oir.currTrace);
                
                // new record
                if (oir.currTrace.getRunID().equals(this.getCurrentRunID()) && oir.currTrace.getOid().equals(this.oysterID)){
                    if (result.isEmpty()) {
                        result = "N";
//                        System.out.println("New record");
                    } else if (result.equals("X")) {
                        if (oir.prevTraces != null && !oir.prevTraces.isEmpty()) {
                            for (Iterator<TraceRecord> it = oir.prevTraces.iterator(); it.hasNext();) {
                                TraceRecord tr = it.next();
//                                System.out.println("Previous Trace:" + tr);
                                
                                if (!tr.getOid().equals(this.oysterID) && (Integer.parseInt(this.getCurrentRunID()))-Integer.parseInt(tr.getRunID()) == 1) {
                                    result = "M";
//                                    System.out.println("Merged record");
                                }
                            }
                        } else {
                        // update record
                            result = "U";
//                            System.out.println("Updated record");
                        }
                    }  else if (result.equals("U")) {
                        if (oir.prevTraces != null && !oir.prevTraces.isEmpty()) {
                            for (Iterator<TraceRecord> it = oir.prevTraces.iterator(); it.hasNext();) {
                                TraceRecord tr = it.next();
//                                System.out.println("Previous Trace:" + tr);
                                
                                if (!tr.getOid().equals(this.oysterID) && (Integer.parseInt(this.getCurrentRunID()))-Integer.parseInt(tr.getRunID()) == 1) {
                                    result = "M";
//                                    System.out.println("Merged record");
                                }
                            }
                        }
                    }
                } else {
                    
                }
            }
        }
        return result;
    }
}
