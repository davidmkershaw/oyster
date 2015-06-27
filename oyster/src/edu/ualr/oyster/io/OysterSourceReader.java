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

import edu.ualr.oyster.OysterExplanationFormatter; 
import edu.ualr.oyster.core.ReferenceItem; 
import edu.ualr.oyster.data.ClusterRecord;
import edu.ualr.oyster.data.ClusterRecordSet;
import edu.ualr.oyster.data.CoDoSAOIR;
import edu.ualr.oyster.data.OysterIdentityRecord;
import edu.ualr.oyster.data.OysterIdentityRecordMap;
import edu.ualr.oyster.data.RecordTypes;
import java.io.IOException;
import java.util.ArrayList;
import java.util.logging.ConsoleHandler;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.logging.Logger; 

/**
 * This is the base data reader class from which all other readers will extend
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.EAFEE659-D4FD-B736-229D-9F0DF6E5E45B]
// </editor-fold> 
public abstract class OysterSourceReader {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.5FC6CC7C-92C7-A494-B45D-EBEC9ABE0C61]
    // </editor-fold> 
    /** An array list of ReferenceItems used to hold the current reference */
    protected ArrayList<ReferenceItem> referenceItems = null;

    /** The ClusterRecord that is presented externally that has the current reference */
    protected ClusterRecord clusterRecord = null;
    
    protected int recordType = 0;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.94CE42DD-B8B8-4515-FB95-C3BB97156AA9]
    // </editor-fold> 
    /** */
    protected boolean debug = false;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.3F2F36F4-51D5-897E-7909-12B40159E43A]
    // </editor-fold> 
    /** */
    protected Logger logger = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.6DCCB06E-041F-505E-F4A5-996A80B8CA6A]
    // </editor-fold> 
    /** */
    protected FileHandler fileHandler = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.03AB037D-7E50-F392-2DD9-A89AE07246C7]
    // </editor-fold> 
    /** */
    protected ConsoleHandler consoleHandler = null;

    /** The current record count */
    protected long recordCount = 1;
    
    /** The point at which to notify how many records have been processed */
    private long countPoint = 10000;
    
    /** The source name */
    protected String source = "";
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.1685DB1B-EDB9-2400-57F3-31F6DB894DFE]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>OysterSourceReader</code>.
     */
    public OysterSourceReader (Logger log) {
        // initialize logger
        this.logger = log;
    }

    /**
     * Creates a new instance of <code>OysterSourceReader</code>.
     */
    public OysterSourceReader (String logFile, Level logLevel) {
        try {

            // initialize logger
            logger = Logger.getLogger(getClass().getName());
            fileHandler = new FileHandler(logFile);
//            consoleHandler = new ConsoleHandler();
            // add handlers
            logger.addHandler(fileHandler);
//            logger.addHandler(consoleHandler);
            // set level and formatter
            logger.setLevel(logLevel);
            OysterExplanationFormatter formatter = new OysterExplanationFormatter();
            fileHandler.setFormatter(formatter);
        } catch (IOException ex) {
            Logger.getLogger(OysterSourceReader.class.getName()).log(Level.SEVERE, null, ex);
        } catch (SecurityException ex) {
            Logger.getLogger(OysterSourceReader.class.getName()).log(Level.SEVERE, null, ex);
        }
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.B6DE3EF8-96D3-4949-8A5D-8C40162F9678]
    // </editor-fold> 
    /**
     * Returns the <code>ReferenceItem</code> for this <code>OysterSourceReader</code>.
     * @return the <code>ReferenceItem</code>.
     */
    public ArrayList<ReferenceItem> getReferenceItems () {
        return referenceItems;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.3AEC11E9-5195-4F72-0264-85ABA4EBECA9]
    // </editor-fold> 
    /**
     * Sets the <code>ReferenceItem</code> for this <code>OysterSourceReader</code>.
     * @param referenceItems the <code>ReferenceItem</code> to be set.
     */
    public void setReferenceItems (ArrayList<ReferenceItem> referenceItems) {
        this.referenceItems = referenceItems;
        
        // FIXME: This was done for convenience but this should be moved out to it's own initialization
        OysterIdentityRecord oysterIdentityRecord;
        
        switch(recordType){
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
        
        clusterRecord.insertRecord(oysterIdentityRecord);
    }
    
    /**
     * Returns the <code>ClusterRecord</code> for this <code>OysterSourceReader</code>.
     * @return the <code>ClusterRecord</code>.
     */
    public ClusterRecord getClusterRecord () {
        return clusterRecord;
    }

    /**
     * Sets the <code>ClusterRecord</code> for this <code>OysterSourceReader</code>.
     * @param clusterRecord the <code>ClusterRecord</code> to be set.
     */
    public void setClusterRecord (ClusterRecord clusterRecord) {
        this.clusterRecord = clusterRecord;
    }
    
// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.06097D05-6BC1-9A20-5678-A5E5FE131C37]
    // </editor-fold>
    /**
     * Returns whether the <code>OysterSourceReader</code> is in debug mode.
     * @return true if the <code>OysterSourceReader</code> is in debug mode, otherwise false.
     */
    public boolean isDebug () {
        return debug;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.89BAFA82-7924-EE1A-D96E-DE66021A2CF8]
    // </editor-fold> 
    /**
     * Enables/disables debug mode for the <code>OysterSourceReader</code>.
     * @param debug true to enable debug mode, false to disable it.
     */
    public void setDebug (boolean debug) {
        this.debug = debug;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.412A5846-39BE-9BCD-C6BB-725E8F178E63]
    // </editor-fold>
    /**
     * getItemCount() is an external method that lets the user get the number of
     * items that were read in the last instance
     * @return count
     */
    public int getItemCount () {
        int count = -1;
        
        if (referenceItems != null) {
            count = referenceItems.size();
        }
        
        return count;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.8EB8B23D-E229-0D26-DB78-1BA6FF78BE84]
    // </editor-fold> 
    /**
     * getItemValue() is an external method that lets user get a specific item
     * value from the last record read by getNextReference()
     * @param index the ordinal position of the item to return
     * @return the item at <code>index(j)</code>
     */
    public String getItemValue (int index) {
        String result = null;
        if (this.referenceItems != null){
            if (index >= 0 && index < this.referenceItems.size()){
                result = this.referenceItems.get(index).getData();
            }
        }
        return result;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.25C3FE24-66D5-9847-753E-488D1BF0A8A7]
    // </editor-fold> 
    /**
     * getItemName() is an external method that lets user get a specific 
     * metadata item from the metadata
     * @param index the ordinal position of the metadata item to return
     * @return the metadata item at <code>index(j)</code>
     */
    public String getltemName (int index) {
        String result = null;
        if (this.referenceItems != null){
            if (index >= 0 && index < this.referenceItems.size()){
                result = this.referenceItems.get(index).getName();
            }
        }
        return result;
    }

    /**
     * Returns the current number of records read from this source.
     * @return the number of records read.
     */
    public long getRecordCount() {
        return recordCount;
    }

    /**
     * Sets the current number of records read from this source.
     * @param recordCount the number of records read to be set.
     */
    public void setRecordCount(long recordCount) {
        this.recordCount = recordCount;
    }

    /**
     * Returns the current number of records the count point is set to.
     * @return the count point number.
     */
    public long getCountPoint() {
        return countPoint;
    }

    /**
     * Sets the current count point number.
     * @param countPoint the count point number to be set.
     */
    public void setCountPoint(long countPoint) {
        this.countPoint = countPoint;
    }
    
    /**
     * Returns the current source name of the records.
     * @return the current source name.
     */
    public String getSource() {
        return source;
    }

    /**
     * Sets the current source name of the records.
     * @param source the current source name to be set.
     */
    public void setSource(String source) {
        this.source = source;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.530E6593-46BA-50B4-0B17-683B2E978E28]
    // </editor-fold> 
    /**
     * This method read the next reference from the datasource, parses the 
     * reference into individual items and stores it as the items in the string 
     * array itemList as the current available reference.
     * @return the number of items found in the reference, zero at end of datasource.
     */
    public abstract int getNextReference ();

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.54010A67-BECE-56BC-B1CB-F982BF5C9263]
    // </editor-fold> 
    /**
     * 
     * @return recordImage
     */
    public abstract String getRecordImage ();
    
    /**
     * This method initializes the data reader and opens the datasource.
     */
    public abstract void open();
    
    /**
     * This method flushes any buffers and closes the connection to the datasource.
     */
    public abstract void close();
}

