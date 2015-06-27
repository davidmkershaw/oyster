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
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.TreeMap;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * This class is used to read the Fixed-width text files.
 * @author Eric D. Nelson
 */
public class OysterFixedWidthReader extends OysterSourceReader{
    /** The input reader */
    private BufferedReader in = null;
    
    /** the filename */
    private String file = null;
    
    /**
     * Creates a new instance of <code>OysterFixedWidthReader</code>.
     */
    public OysterFixedWidthReader(Logger log){
        super(log);
    }
    
    /**
     * Creates a new instance of <code>OysterFixedWidthReader</code>.
     * @param file the path to the delimited source file.
     * @param ri the ArrayList of <code>ReferenceItems</code> that will be used to
     * store the parsed data.
     */
    public OysterFixedWidthReader (String file, ArrayList<ReferenceItem> ri, Logger log) {
        super(log);
        
        this.file = file;
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
     * getNextReference() is an external method that reads a reference
     * from the Reference Source, parses the reference into individual items and
     * store the items in the string array itemList
     * @return the number of items it found, zero at EOF
     */
    @Override
    public int getNextReference() {
        int count = 0;
        String read = "", text;
        
        try {
            if ((read = getIn().readLine()) != null){
                // check to see if line is blank if then read the next line
                while (read.isEmpty()){
                    read = in.readLine();
                    
                    if (read == null) {
                        return count;
                    }
                }
                
                text = read;
                
                // clear refererence items
                for (int i = 0; i < getItemCount(); i++) {
                    ReferenceItem item = referenceItems.get(i);
                    item.setData("");
                }
                
                for (int i = 0; i < getItemCount(); i++) {
                    ReferenceItem item = referenceItems.get(i);

                    if (item == null) {
                        item = new ReferenceItem();
                    }
                    
                    String token = split(text, item);
                    // if there are multiple items with the same item name 
                    // concatenate if the items are different
                    if (item.getData() != null && !item.getData().equals("")) {
                        if (item.getData().equalsIgnoreCase(token)) {
                            continue;
                        } else {
                            item.setData(item.getData() + "|" + token);
                        }
                    } else {
                        item.setData(token);
                    }
                    // TODO: Add flag that is set from XML script to enable/disable this derived input RefID
                    if (item.getAttribute().equals("@RefID")){ 
                        if (item.getData() != null && !item.getData().equals("")){
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
            Logger.getLogger(OysterFixedWidthReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        
        return count;
    }

    @Override
    public String getRecordImage() {
        throw new UnsupportedOperationException("Not supported yet.");
    }

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
                tm.put(item.getStart(), item.getName() + "=" + item.getData());
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
    
    /**
     * This method returns the data for a specific <code>ReferenceItem</code>.
     * @param text the test to be parsed.
     * @param item the <code>ReferenceItem</code> to parse from the data stream.
     * @return the data value for the input <code>ReferenceItem</code>.
     */
    private String split(String text, ReferenceItem item) {
        String result = null;
        
        if (text != null && text.length() >= item.getEnd()){
            result = text.substring(item.getStart()-1, item.getEnd()).trim();
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
        } catch (IOException ex) {
            Logger.getLogger(OysterFixedWidthReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
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
        } catch (IOException ex) {
            Logger.getLogger(OysterFixedWidthReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }
}
