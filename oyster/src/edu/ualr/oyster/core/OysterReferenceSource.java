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

package edu.ualr.oyster.core;

import edu.ualr.oyster.io.OysterSourceReader; 
import java.util.ArrayList;  
import java.util.Iterator;

/**
 * Interface to a set of entity references as implemented by the system
 * Responsibilities:
 * <ul>
 * <li>Convert an XML description of a reference source from to an 
 * OysterReferenceSource object</li>
 * <li>Allows other objects to read the references in the source in sequential 
 * order</li>
 * </ul>
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.69A89066-9BF4-A8B0-9A85-A0755B269C0D]
// </editor-fold> 
public class OysterReferenceSource {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.773B0582-860A-C064-717D-1933826A65E0]
    // </editor-fold> 
    /** The source reader that will read this source */
    private OysterSourceReader sourceReader = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.1F23124C-CEF8-85DC-781C-2FF6862CCB47]
    // </editor-fold> 
    /** */
    private boolean debug = false;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.7C9F1CB1-A97D-B5B7-73B7-56D5421DCA2B]
    // </editor-fold> 
    /** The name of the source */
    private static String sourceName = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.0207FD1F-6812-8D69-AFAF-FE8FE3163673]
    // </editor-fold> 
    /** The path to where the source exist if it is on a file system */
    private static String sourcePath = null;
    
    /** The type of the source, i.e. delimited file */
    private static String sourceType = null;
    
    /** The delimiter to use on a delimited file */
    private static String delimiter = null;
    
    /** The qualifer to use if the file is delimited */
    private static String qualifer = null;
    
    /** The label to use if the file is delimited */
    private static boolean label = false;
    
    /** The server name or IP address to use when connecting to the database */
    private static String server = null;
    
    /** The port that the database will be listening on */
    private static String port = null;
    
    /** The service id/name of the database */
    private static String sid = null;
    
    /** The user name needed to log into the database */
    private static String userID = null;
    
    /** The password to use when logging on to the database */
    private static String passwd = null;
    
    /** The database connection type */
    private static String connectionType = "ODBC";
    
    /** The custom SQL string to run */
    private static String overRideSQL = null;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.F200947E-D735-25CB-B1D0-682AE3488F03]
    // </editor-fold> 
    /** The array that will hold the input references */
    private static ArrayList<ReferenceItem> referenceItems = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.C85E7AFC-B015-BCD4-9ADA-1C3EC5F76D98]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>OysterReferenceSource</code>
     */
    public OysterReferenceSource () {
        referenceItems = new ArrayList<ReferenceItem>();
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.900A37C0-BB38-65ED-F7D0-9A1EE38624AF]
    // </editor-fold> 
    /**
     * Returns the <code>OysterSourceReader</code> for this <code>OysterReferenceSource</code>
     * @return the <code>OysterSourceReader</code>
     */
    public OysterSourceReader getSourceReader () {
        return sourceReader;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.0B1A60AC-211C-5598-053D-49F5384D2F88]
    // </editor-fold> 
    /**
     * Sets the <code>OysterSourceReader</code> for this <code>OysterReferenceSource</code>
     * @param aSourceReader the <code>OysterSourceReader</code> to be set.
     */
    public void setSourceReader (OysterSourceReader aSourceReader) {
        this.sourceReader = aSourceReader;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.C94E3991-93A7-A972-A38A-538A68BAAE54]
    // </editor-fold> 
    /**
     * Returns the source name for this <code>OysterReferenceSource</code>.
     * @return the source name.
     */
    public String getSourceName () {
        return sourceName;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.94F09E0B-C8C5-BEAC-EE2A-937AE29772BC]
    // </editor-fold> 
    /**
     * Sets the source name for this <code>OysterReferenceSource</code>.
     * @param aSourceName the source name to be set.
     */
    public void setSourceName (String aSourceName) {
        sourceName = aSourceName;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.C9911B78-BF90-7E82-9704-95155B3874E3]
    // </editor-fold> 
    /**
     * Returns the source path for this <code>OysterReferenceSource</code>.
     * @return the source path.
     */
    public String getSourcePath () {
        return sourcePath;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.59816F18-7677-302C-D4EA-0E2FA5969372]
    // </editor-fold> 
    /**
     * Sets the source path for this <code>OysterReferenceSource</code>.
     * @param aSourcePath the source path to be set.
     */
    public void setSourcePath (String aSourcePath) {
        sourcePath = aSourcePath;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.C3351BCF-F6B5-3B65-7A48-BC9ABCD3D886]
    // </editor-fold> 
    /**
     * Returns the source type for this <code>OysterReferenceSource</code>.
     * @return the source type.
     */
    public String getSourceType () {
        return sourceType;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.E9738B4D-9750-615D-4B59-BB020A369B98]
    // </editor-fold> 
    /**
     * Sets the source type for this <code>OysterReferenceSource</code>.
     * @param aSourceType The source type to be set.
     */
    public void setSourceType (String aSourceType) {
        sourceType = aSourceType;
    }
    
    /**
     * Returns the delimiter for this <code>OysterReferenceSource</code>.
     * @return the delimiter.
     */
    public String getDelimiter() {
        return delimiter;
    }

    /**
     * Sets the delimiter for this <code>OysterReferenceSource</code>.
     * @param aDelimiter the delimiter to be set.
     */
    public void setDelimiter(String aDelimiter) {
        delimiter = aDelimiter;
    }

    /**
     * Returns the text qualifier for this <code>OysterReferenceSource</code>.
     * @return the qualifier.
     */
    public String getQualifer() {
        return qualifer;
    }

    /**
     * Sets the text qualifier for this <code>OysterReferenceSource</code>.
     * @param aQualifer the text qualifier to be set.
     */
    public void setQualifer(String aQualifer) {
        qualifer = aQualifer;
    }

    /**
     * Returns whether the OysterReferenceSource is in debug mode.
     * @return true if the OysterReferenceSource is in debug mode, otherwise false.
     */
    public boolean isLabel() {
        return label;
    }

    /**
     * Enables/disables debug mode for the OysterReferenceSource.
     * @param aLabel true to enable debug mode, false to disable it.
     */
    public void setLabel(boolean aLabel) {
        label = aLabel;
    }

    /**
     * Returns the server address for this <code>OysterReferenceSource</code>.
     * @return the server address.
     */
    public String getServer() {
        return server;
    }

    /**
     * Sets the server address for this <code>OysterReferenceSource</code>.
     * @param aServer the server address to be set.
     */
    public void setServer(String aServer) {
        server = aServer;
    }

    /**
     * Returns the port number for the server for this <code>OysterReferenceSource</code>.
     * @return the port number.
     */
    public String getPort() {
        return port;
    }

    /**
     * Sets the port number for the server for this <code>OysterReferenceSource</code>.
     * @param aPort the port number to be set.
     */
    public void setPort(String aPort) {
        port = aPort;
    }

    /**
     * Returns the Database name (SID) for this <code>OysterReferenceSource</code>.
     * @return the sid
     */
    public String getSid() {
        return sid;
    }

    /**
     * Sets the Database name (SID) for this <code>OysterReferenceSource</code>.
     * @param aSid the database name to be set.
     */
    public void setSid(String aSid) {
        sid = aSid;
    }

    /**
     * Returns the UserID for the <code>OysterReferenceSource</code>.
     * @return the userID.
     */
    public String getUserID() {
        return userID;
    }

    /**
     * Sets the UserID for the <code>OysterReferenceSource</code>.
     * @param aUserID the UserID to be set.
     */
    public void setUserID(String aUserID) {
        userID = aUserID;
    }

    /**
     * Returns the password for this <code>OysterReferenceSource</code>.
     * @return the password.
     */
    public String getPasswd() {
        return passwd;
    }

    /**
     * Sets the password for this <code>OysterReferenceSource</code>.
     * @param aPasswd the password to be set.
     */
    public void setPasswd(String aPasswd) {
        passwd = aPasswd;
    }
    
    /**
     * Returns the connection type for this <code>OysterReferenceSource</code>.
     * @return the connection type to be returned.
     */
    public String getConnectionType() {
        return connectionType;
    }

    /**
     * Sets the connection type for this <code>OysterReferenceSource</code>.
     * @param aConnectionType the connection type to be set.
     */
    public void setConnectionType(String aConnectionType) {
        connectionType = aConnectionType;
    }
    
    /**
     * Returns the overRideSQL for this <code>OysterDatabaseReader</code>.
     * @return the overRideSQL.
     */
    public String getOverRideSQL() {
        return overRideSQL;
    }

    /**
     * Sets the overRideSQL for this <code>OysterDatabaseReader</code>.
     * @param aOverRideSQL the overRideSQL to be set.
     */
    public void setOverRideSQL(String aOverRideSQL) {
        overRideSQL = aOverRideSQL;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.1F57C935-B12B-DBCC-BE95-4525701FC4D0]
    // </editor-fold> 
    /**
     * Returns the reference items for this <code>OysterReferenceSource</code>.
     * @return the reference items.
     */
    public ArrayList<ReferenceItem> getReferenceItems () {
        return referenceItems;
    }

    /**
     * Returns a <code>ReferenceItem</code> that matches the input itemName
     * @param itemName
     * @return matched <code>ReferenceItem</code>.
     */
    public ReferenceItem getReferenceItemByItemName(String itemName){
        ReferenceItem ri = null;
        
        for (Iterator<ReferenceItem> it = referenceItems.iterator(); it.hasNext();){
            ri = it.next();
            
            if (itemName.equalsIgnoreCase(ri.getName())) {
                break;
            }
        }
        return ri;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.3C55C4F6-5F60-D26E-57B2-559F6201D926]
    // </editor-fold> 
    /**
     * Sets the reference items for this <code>OysterReferenceSource</code>.
     * @param aReferenceItems the reference Items to be set.
     */
    public void setReferenceItems (ArrayList<ReferenceItem> aReferenceItems) {
        referenceItems = aReferenceItems;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.D400D35F-1DCE-E854-BB09-9AB86CDFB4C1]
    // </editor-fold> 
    /**
     * This method will read the next reference into the referenceItems.
     * @return the number of referenceItems read.
     */
    public int getNextReference () {
        return 0;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.608010B0-E628-A9D9-3577-8E75FA96254D]
    // </editor-fold> 
    /**
     * This method returns the value found at position index.
     * @param index
     * @return null
     */
    public String getValueAtPosition (int index) {
        return null;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.A6AAC5C3-75FB-ABFA-3088-C12EC9BE8E31]
    // </editor-fold> 
    /**
     * This method returns the value associated with attribute item.
     * @param item
     * @return null
     */
    public String getValueOfltem (String item) {
        return null;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.CA246B2B-AA2F-5561-C648-4A9427368154]
    // </editor-fold> 
    /**
     * 
     * @return null
     */
    public String getRecordImage () {
        return null;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.FC04B896-46B1-A5B6-702E-BE094ED5FA91]
    // </editor-fold> 
    /**
     * 
     * @param index
     * @return null
     */
    public String getAttributeOfPosition (int index) {
        return null;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.3F107DFF-03C8-783F-2E5C-F8EB5647CAA3]
    // </editor-fold> 
    /**
     * 
     * @param item
     * @return null
     */
    public String getPositionOfltem (String item) {
        return null;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.DE725BB2-4899-005C-7268-A11318EDEDDD]
    // </editor-fold> 
    /**
     * 
     * @param item
     * @return null
     */
    public String getAttrOfltem (String item) {
        return null;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.E4361F1A-06D0-6FEA-B047-C74F9DDCEA9B]
    // </editor-fold> 
    /**
     * Returns whether the <code>OysterReferenceSource</code> is in debug mode.
     * @return true if the <code>OysterReferenceSource</code> is in debug mode, otherwise false.
     */
    public boolean isDebug () {
        return debug;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.09D217E1-F141-F9E0-BDCE-59BF2FA5534D]
    // </editor-fold> 
    /**
     * Enables/disables debug mode for the <code>OysterReferenceSource</code>.
     * @param debug true to enable debug mode, false to disable it.
     */
    public void setDebug (boolean debug) {
        this.debug = debug;
    }

    /**
     * Adds the specified reference item to the end of this ArrayList, 
     * increasing its size by one.
     * @param item the item to be added.
     */
    public void addReferenceItem(ReferenceItem item){
        referenceItems.add(item);
    }
}

