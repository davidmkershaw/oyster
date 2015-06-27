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

package edu.ualr.oyster.io;

import edu.ualr.oyster.ErrorFormatter;
import edu.ualr.oyster.core.ReferenceItem;
import edu.ualr.oyster.data.ClusterRecordSet;
import edu.ualr.oyster.data.CoDoSAOIR;
import edu.ualr.oyster.data.OysterIdentityRecord;
import edu.ualr.oyster.data.OysterIdentityRecordMap;
import edu.ualr.oyster.data.RecordTypes;
import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.TreeMap;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * This class is used to read the Delimited text files.
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.F3E85D9E-12E2-A8CE-0C0D-56734748CCAA]
// </editor-fold> 
public class OysterDelimitedReader extends OysterSourceReader {
    /** The input reader */
    private BufferedReader in = null;
    
    /** the filename */
    private String file = "";
    
    /** the field delimiter */
    private String delimiter = "";
    
    /** the quote qualifier */
    private String qualifier = "";
    
    /** the header flag */
    private boolean header = false;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.AD222E0A-7E1A-DFE8-D2A5-14ECE3D360E7]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>OysterDelimitedReader</code>.
     */
    public OysterDelimitedReader (Logger log) {
        super(log);
    }

    /**
     * Creates a new instance of <code>OysterDelimitedReader</code>.
     * @param file the path to the delimited source file.
     * @param delimiter the field delimiter used within the file.
     * @param qualifier true if the file uses a quote qualifier, otherwise false.
     * @param header true if the file has a header record, otherwise false.
     * @param ri the ArrayList of <code>ReferenceItems</code> that will be used to
     * store the parsed data.
     */
    public OysterDelimitedReader (String file, String delimiter, String qualifier, boolean header, ArrayList<ReferenceItem> ri, Logger log) {
        super(log);
        
        this.file = file;
        this.setDelimiter(delimiter);
        this.qualifier = qualifier;
        this.header = header;
        
        setReferenceItems(ri);
    }
    
    /**
     * Returns the <code>BufferedReader</code> for this <code>OysterDelimitedReader</code>.
     * @return the <code>BufferedReader</code>.
     */
    public BufferedReader getIn() {
        return in;
    }

    /**
     * Sets the <code>BufferedReader</code> for this <code>OysterDelimitedReader</code>.
     * @param in the <code>BufferedReader</code> to be set.
     */
    public void setIn(BufferedReader in) {
        this.in = in;
    }

    /**
     * Returns the filepath for this <code>OysterDelimitedReader</code>.
     * @return the filepath.
     */
    public String getFile() {
        return file;
    }

    /**
     * Sets the filepath for this <code>OysterDelimitedReader</code>.
     * @param file the filepath to be set.
     */
    public void setFile(String file) {
        this.file = file;
    }
    
    /**
     * Returns the delimiter for this <code>OysterDelimitedReader</code>.
     * @return the delimiter.
     */
    public String getDelimiter() {
        return delimiter;
    }

    /**
     * Sets the delimiter for this <code>OysterDelimitedReader</code>.
     * @param delimiter the delimiter to be set.
     */
    public final void setDelimiter(String delimiter) {
        if (delimiter.equals("[tab]")) {
            this.delimiter = "\t";
        } else if (delimiter.equals("\\t")) {
            this.delimiter = "\t";
        } else if (delimiter.startsWith("\\u")){
            this.delimiter = delimiter.substring(1);
        } else {
            this.delimiter = delimiter;
        }
    }

    /**
     * Returns the qualifier for this <code>OysterDelimitedReader</code>.
     * @return the qualifier.
     */
    public String getQualifier() {
        return qualifier;
    }

    /**
     * Sets the qualifier for this <code>OysterDelimitedReader</code>.
     * @param qualifier the qualifier to be set.
     */
    public void setQualifier(String qualifier) {
        this.qualifier = qualifier;
    }

    /**
     * Returns whether the source file has a header.
     * @return true if the source file has a header, otherwise false.
     */
    public boolean isHeader() {
        return header;
    }

    /**
     * Enables/disables whether the source file has a header.
     * @param header true if the source file has a header, otherwise false.
     */
    public void setHeader(boolean header) {
        this.header = header;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.529F49B3-9999-B275-044F-0026C1440364]
    // </editor-fold> 
    /**
     * getNextReference() is an external method that reads a reference
     * from the Reference Source, parses the reference into individual items and
     * store the items in the string array itemList
     * @return the number of items it found, zero at EOF
     */
    @Override
    public int getNextReference () {
        int count = 0;
        String read = "";
        LinkedHashMap<String, String> text;
        
        try {
            if ((read = in.readLine()) != null){
                // check to see if line is blank if then read the next line
                while (read.trim().isEmpty()){
                    read = in.readLine();
                    
                    if (read == null) {
                        return count;
                    }
                }
                
                if (header) {
                    read = in.readLine();
                    header = false;
                }
                
                if (qualifier.equals("")) {
                    text = split(read);
                } else {
                    text = split2(read);
                }
                
                for (int i = 0; i < getItemCount(); i++) {
                    ReferenceItem item = referenceItems.get(i);

                    if (item == null) {
                        item = new ReferenceItem();
                    }
                    item.setData(text.get(item.getName()));
                    // TODO: Add flag that is set from XML script to enable/disable this derived input RefID
                    if (item.getAttribute().equals("@RefID")) {
                        if (item.getData() != null && !item.getData().equals("")) {
                            item.setData(source + "." + item.getData());
                        } else {
                            item.setData(source + ".D" + this.recordCount);
                        }
                    }
                    
                    referenceItems.set(i, item);
                    count++;
                }
                
                OysterIdentityRecord oysterIdentityRecord;
                
                switch (recordType) {
                    case RecordTypes.CODOSA:
                        oysterIdentityRecord = new CoDoSAOIR();
                        break;
                    case RecordTypes.MAP:
                        oysterIdentityRecord = new OysterIdentityRecordMap();
                        break;
                    default:
                        oysterIdentityRecord = new OysterIdentityRecordMap();
                }
                
                oysterIdentityRecord.convertToOIR(referenceItems);
                if (clusterRecord == null) {
                    clusterRecord = new ClusterRecordSet(recordType);
                }
                
                clusterRecord.clear();
                clusterRecord.insertRecord(oysterIdentityRecord);
                
                if (recordCount % getCountPoint() == 0) {
                    System.out.println(recordCount + "...");
                }
                
                recordCount++;
            }
        } catch (IOException ex) {
            System.err.println(read);
            Logger.getLogger(OysterDelimitedReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        
        return count;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.6596E5EF-7180-C270-96F0-0EAB40EFD39E]
    // </editor-fold> 
    @Override
    public String getRecordImage () {
        throw new UnsupportedOperationException("Not supported yet.");
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.C7E3752F-EC5C-65D2-9992-9FC628A31D8D]
    // </editor-fold> 
    /**
     * Returns a string representation of the current record with 0x07 field delimiter
     * @return the current record as a 0x07 delimited string
     */
    public String getRecordImageAsDelimitedString () {
        StringBuilder result = new StringBuilder(250);
        if (getItemCount() > 0){
            TreeMap<Integer, String> tm = new TreeMap<Integer, String>();
            for (int i = 0; i < getItemCount(); i++){
                ReferenceItem item = referenceItems.get(i);
                tm.put(item.getOrdinal(), item.getData());
            }
            
            Iterator<Integer> it = tm.keySet().iterator();
            int key = it.next();
            String value = tm.get(key);
            result.append(value);
            
            do {
                key = it.next();
                value = tm.get(key);
                
                result.append("\u0007").append(value);
            } while (it.hasNext());
        }
        
        return result.toString();
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.5F7D0047-0587-A7D1-DC6E-279256BF4E19]
    // </editor-fold> 
    /**
     * Returns the keyword value pairs of the current record. Each pair is delimited
     * by the bell (0x07) character
     * @return the current record as attribute/value pairs
     */
    public String getRecordImageAsKeyValuePair() {
        StringBuilder result = new StringBuilder(250);
        if (getItemCount() > 0){
            TreeMap<Integer, String> tm = new TreeMap<Integer, String>();
            for (int i = 0; i < getItemCount(); i++){
                ReferenceItem item = referenceItems.get(i);
                tm.put(item.getOrdinal(), item.getName() + "=" + item.getData());
            }
            
            Iterator<Integer> it = tm.keySet().iterator();
            int key = it.next();
            String value = tm.get(key);
            result.append(key).append("=").append(value);
            
            do {
                key = it.next();
                value = tm.get(key);
                
                result.append("\u0007").append(key).append("=").append(value);
            } while (it.hasNext());
        }
        
        return result.toString();
    }
    
    /**
     * This method parses that data into separate distinct values separated by
     * the set delimiter.
     * @param record the record to be split.
     * @return HashMap containing the logical name data value as keyword value 
     * pairs.
     */
    private LinkedHashMap<String, String> split(String record) {
        int begin, count = 0;
        ArrayList<String> al = new ArrayList<String>();
        LinkedHashMap<String, String> result = new LinkedHashMap<String, String>();
        try {
            while ((begin = record.indexOf(delimiter)) > -1) {
                count++;

                String token = record.substring(0, begin);
                record = record.substring(begin + 1);
                al.add(token);
            }
            //if (record.compareTo("") != 0)
            al.add(record);

            // clear refererence items
            for (int i = 0; i < getItemCount(); i++) {
                ReferenceItem item = referenceItems.get(i);
                item.setData("");
            }

            for (int i = 0; i < getItemCount(); i++) {
                ReferenceItem item = referenceItems.get(i);
                // if there are multiple items with the same item name 
                // concatenate if the items are different
                if (result.containsKey(item.getName())) {
                    if (result.get(item.getName()).equalsIgnoreCase(al.get(item.getOrdinal()).trim())) {
                        result.put(item.getName(), al.get(item.getOrdinal()).trim());
                    } else {
                        result.put(item.getName(), result.get(item.getName()) + "|" + al.get(item.getOrdinal()).trim());
                    }
                } else {
                    if (al.size() > item.getOrdinal()) {
                        result.put(item.getName(), al.get(item.getOrdinal()).trim());
                    } else {
                        result.put(item.getName(), null);
                    }
                }
            }
        } catch (RuntimeException ex) {
            Logger.getLogger(OysterDelimitedReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return result;
    }
    
    /**
     * This method parses that data into separate distinct values separated by
     * the set delimiter. This method correctly handles quote qualified records.
     * @param record the record to be split.
     * @return HashMap containing the logical name data value as keyword value 
     * pairs.
     */
    private LinkedHashMap<String, String> split2(String record) {
        ArrayList<String> v = new ArrayList<String>();
        String token = "";
        boolean open = false, close = false;
        LinkedHashMap<String, String> result = new LinkedHashMap<String, String>();

        try {
            for (int i = 0; i < record.length(); i++) {
                if (record.charAt(i) == qualifier.charAt(0)) {
                    if (!open) {
                        open = true;
                    } else if (open) {
                        close = true;
                    }
                } else if (record.charAt(i) == delimiter.charAt(0)) {
                    if (open && close) {
                        token = token.replaceAll("[" + qualifier + "]", "").trim();
                        v.add(token);
                        token = "";
                        open = false;
                        close = false;
                    } else if (!open && !close) {
                        v.add(token);
                        token = "";
                    } else if (open && !close) {
                        token += record.charAt(i);
                    }
                } else {
                    token += record.charAt(i);
                }
            }
            v.add(token);

            // clear refererence items
            for (int i = 0; i < getItemCount(); i++) {
                ReferenceItem item = referenceItems.get(i);
                item.setData("");
            }

            for (int i = 0; i < getItemCount(); i++) {
                ReferenceItem item = referenceItems.get(i);
                if (result.containsKey(item.getName())) {
                    if (result.get(item.getName()).equalsIgnoreCase(v.get(item.getOrdinal()).trim())) {
                        result.put(item.getName(), v.get(item.getOrdinal()).trim());
                    } else {
                        result.put(item.getName(), result.get(item.getName()) + "|" + v.get(item.getOrdinal()).trim());
                    }
                } else {
                    if (v.size() > item.getOrdinal()) {
                        result.put(item.getName(), v.get(item.getOrdinal()).trim());
                    } else {
                        result.put(item.getName(), null);
                    }
                }
            }
        } catch (RuntimeException ex) {
            Logger.getLogger(OysterDelimitedReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return result;
    }

    /**
     * This method initializes the file reader and opens the file if it exist.
     */
    @Override
    public void open() {
        try {
            in = new BufferedReader(new InputStreamReader(new FileInputStream(this.file), "UTF8"));
        } catch (FileNotFoundException ex) {
            Logger.getLogger(OysterDelimitedReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch (UnsupportedEncodingException ex) {
            Logger.getLogger(OysterDelimitedReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }

    /**
     * This method flushes any buffers and closes the file reader.
     */
    @Override
    public void close() {
        try {
            if (in != null) {
                in.close();
            }
        }
        catch (IOException ex) {
            Logger.getLogger(OysterDelimitedReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }
}

