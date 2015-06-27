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
import edu.ualr.oyster.data.ClusterRecord;
import edu.ualr.oyster.data.ClusterRecordSet;
import edu.ualr.oyster.data.CoDoSAOIR;
import edu.ualr.oyster.data.OysterIdentityRecord;
import edu.ualr.oyster.data.OysterIdentityRecordMap;
import edu.ualr.oyster.data.RecordTypes;
import edu.ualr.oyster.kb.ModificationRecord;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.sql.Types;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.TimeZone;
import java.util.TreeMap;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import org.xml.sax.Attributes;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

/**
 * This class is used to parse the Identity XML file and return an Entity Map,
 * a Value Index and a LinkMap (only if the append flag is set).
 * @author Eric D. Nelson
 */
public class DBIdentityParser extends OysterXMLParser {
    private Connection conn;
    private PreparedStatement pstmt;
    
    /** The <code>ClusterRecord</code> used during parsing */
    private ClusterRecord identity = null;
    
    /** The <code>OysterIdentityRecord</code> used during parsing */
    private OysterIdentityRecord oir = null;
    
    /** */
    private static HashMap<String, Long> size = null;
    
    /** Used to hold the current XML parent tag */
    private String parent = "";
    
    /** The id used during parsing */
    private String id = "";
    
    /** The name used during parsing */
    private String name = "";
    
    /** The tag used during parsing */
    private String tag = "";
    
    /** The value used during parsing */
    private String value = "";
    
    /** The count of clusters read */
    private int count = 1;
    
    /** */
    private TreeMap<Integer, String> metadata = new TreeMap<Integer, String>();
    
    /** The previous modifications to be populated*/
    private static TreeMap<String, ModificationRecord> mods = null;

    /** The <code>ModificationRecord</code> used during parsing */
    private static ModificationRecord mr = null;

    /** Date Format used to parse the modification dates */
    private SimpleDateFormat sdf = null;
    
    /** The number of clusters read */
    private static int clusterCount = 0;
    
    /** The number of references read */
    private static int referenceCount = 0;
    
    private int recordType = 0, counter = 0, total = 0;
    
    /** */
    private Logger logger = null;
    
    /**
     * Creates a new instance of <code>IdentityParser</code>.
     * @param conn Connection 
     * @param pstmt PreparedStatement
     * @param logger Logger
     * @param recordType
     */
    public DBIdentityParser (Connection conn, PreparedStatement pstmt, Logger logger, int recordType) {
        super();
        this.conn = conn;
        this.pstmt = pstmt;
        this.logger = logger;
        this.recordType = recordType;
        
        mods = new TreeMap<String, ModificationRecord>();
        
        String DATE_FORMAT = "yyyy-MM-dd";
        sdf = new java.text.SimpleDateFormat(DATE_FORMAT);
        sdf.setTimeZone(TimeZone.getDefault());
    }
    
    /**
     * Returns the size of the identity repository found by this <code>IdentityParser</code>.
     * @return the size found
     */
    public int getSize(){
        return size.size();
    }
    
    /**
     * Returns a list of the parsed modifications.
     * @return mods
     */
    public TreeMap<String, ModificationRecord> getModifications() {
        return mods;
    }
    
    /**
     * Returns the total number of clusters parsed.
     * @return clusterCount
     */
    public int getClusterCount() {
        return clusterCount;
    }

    /**
     * Returns the total number of references parsed.
     * @return referenceCount
     */
    public int getReferenceCount() {
        return referenceCount;
    }

    /**
     * Returns the current system time
     * @return the current system time
     */
    private Date now(){
        Date result;
        Calendar cal = Calendar.getInstance(TimeZone.getDefault());

        result = cal.getTime();
        return result;
    }
    
    
    //==========================================================================
    //  ... XML SAX Parsing methods
    //==========================================================================
    /**
     * Called when the Parser starts parsing the Current XML File. Handle any
     * document specific initialization code here.
     * @throws org.xml.sax.SAXException
     */
    @Override
    public void startDocument () throws org.xml.sax.SAXException {
    }

    /**
     * Called when the Parser Completes parsing the Current XML File. Handle any
     * document specific clean up code here.
     * @throws org.xml.sax.SAXException
     */
    @Override
    public void endDocument () throws org.xml.sax.SAXException {
    }

    /**
     * Called when the starting of the Element is reached. For Example if we have
     * Tag called <Title> ... </Title>, then this method is called when <Title>
     * tag is Encountered while parsing the Current XML File. The attrs Parameter 
     * has the list of all Attributes declared for the Current Element in the 
     * XML File.
     * @param namespaceURI URI for this namespace
     * @param lName local XML name
     * @param qName qualified XML name
     * @param attrs list of all Attributes declared for the Current Element
     * @throws org.xml.sax.SAXException
     */
    @Override
    public void startElement (String namespaceURI, String lName, String qName, Attributes attrs) throws org.xml.sax.SAXException {
        String eName = lName; // element name 
        if ("".equals(eName)) {
            eName = qName;
        } 
/*
        if (count > 160000){
            emit("Tag: " + eName);
            nl();
        }
*/
        // clear the data
        data = "";
        
        if (eName.equalsIgnoreCase("Identity")){
            identity = new ClusterRecordSet(recordType);
            identity.setPersistant(true);
        } else if (eName.equalsIgnoreCase("Creation")){
            identity = new ClusterRecordSet(recordType);
            mr = new ModificationRecord();
        } else if (eName.equalsIgnoreCase("Modification")){
            identity = new ClusterRecordSet(recordType);
            mr = new ModificationRecord();
        } else if (eName.equalsIgnoreCase("StrToStr")){
            parent = eName;
        } else if (eName.equalsIgnoreCase("negStrToStr")){
            parent = eName;
        }
        
        // get XML attributes
        if (attrs != null) { 
            for (int i = 0; i < attrs.getLength(); i++) { 
                String aName = attrs.getLocalName(i); 
                // Attr name 
                if ("".equals(aName)) {
                    aName = attrs.getQName(i);
                } 
                
                String token = attrs.getValue(i).trim();
/*
                if (count > 160000){
                    emit("\t" + aName + ": " + token);
                    nl();
                }
*/
                if(aName.equalsIgnoreCase("Identifier")){
                    id = token;
                    identity.setOysterID(id);
                } else if(aName.equalsIgnoreCase("Name")){
                    name = token;
                } else if(aName.equalsIgnoreCase("Tag")){
                    tag = token;
                } else if(aName.equalsIgnoreCase("Value")){
                    value = token;
                    
                    switch (recordType) {
                        case RecordTypes.CODOSA:
                            oir = new CoDoSAOIR();
                            break;
                        case RecordTypes.MAP:
                            oir = new OysterIdentityRecordMap();
                            break;
                        default:
                            oir = new OysterIdentityRecordMap();
                    }
                } else if(aName.equalsIgnoreCase("OysterVersion")){
                    mr.setOysterVersion(token);
                } else if(aName.equalsIgnoreCase("Date")){
                    mr.setDate(token);
                } else if(aName.equalsIgnoreCase("RunScript")){
                    mr.setRunScriptName(token);
                } else if(aName.equalsIgnoreCase("CDate")){
                    Date creationDate;
                    try {
                        creationDate = sdf.parse(token);
                    } catch (ParseException ex) {
                        Logger.getLogger(DBIdentityParser.class.getName()).log(Level.SEVERE, null, ex);
                        
                        creationDate = now();
                    }
                    identity.setCreationDate(creationDate);
                }
            }
        }
    }
    
    /**
     * Called when the Ending of the current Element is reached. For example in 
     * the above explanation, this method is called when </Title> tag is reached
     * @param namespaceURI URI for this namespace
     * @param sName
     * @param qName qualified XML name
     * @throws org.xml.sax.SAXException
     */
    @SuppressWarnings( "unchecked" )
    @Override
    public void endElement (String namespaceURI, String sName, String qName) throws org.xml.sax.SAXException {
        String eName = sName; // element name 
        if ("".equals(eName)) {
            eName = qName;
        } 
/*
        if (count > 160000){
            if (!data.equals("")){
                emit("Data: " + data);
                nl();
            }
        }
*/
        if (eName.equalsIgnoreCase("Identity")){
            // HashMap<String, ClusterRecord> entityMap
            
            // insert cluster
            insert();
            
            if (count % 10000 == 0) {
                System.out.println("Loading " + count + "...");
                
                try {
                    conn.commit();
                } catch (SQLException ex) {
                    Logger.getLogger(DBIdentityParser.class.getName()).log(Level.SEVERE, null, ex);
                }
            }
            count++;
            
            clusterCount++;
        } else if (eName.equalsIgnoreCase("Attribute")){
            this.identity.updateMetaData(name, tag);
            name = "";
            tag = "";
        } else if (eName.equalsIgnoreCase("Reference")){
            String [] temp = value.split("[|]");
            
            for (int i = 0; i < temp.length; i++){
                String [] temp2 = temp[i].split("[\\^]");
                oir.add(identity.getAttributeNameByTag(temp2[0]), temp2[1]);
            }
            oir.setInput(true);
            identity.insertRecord(oir);
            referenceCount++;
            value = "";
        } else if (eName.equalsIgnoreCase("Creation")){
            mods.put(mr.getDate(), mr);
        } else if (eName.equalsIgnoreCase("Modification")){
            mods.put(mr.getDate(), mr);
        } else if (eName.equalsIgnoreCase("OID")){
            if (parent.equalsIgnoreCase("StrToStr")) {
                identity.getStrToStr().add(data);
            } else if (parent.equalsIgnoreCase("NegStrStr")) {
                identity.getNegStrToStr().add(data);
            }
        } else if (eName.equalsIgnoreCase("StrToStr")){
            parent = "";
        } else if (eName.equalsIgnoreCase("NegStrStr")){
            parent = "";
        }
    }
    
    //==========================================================================
    //  ... Database Methods
    //==========================================================================
    private void insert(){
        int rc;
        
        try {
            for (int i = 0; i < identity.getSize(); i++){
                OysterIdentityRecord o = identity.getOysterIdentityRecord(i);
                pstmt.setString(1, identity.getOysterID());
                
                for (Iterator<Integer> it = metadata.keySet().iterator(); it.hasNext();){
                    int key = it.next();
                    String item = metadata.get(key);
                    String token = o.get(item);
                    
                    if (token != null) {
                        pstmt.setString(key, token);
                    } else {
                        pstmt.setNull(key, Types.VARCHAR);
                    }
                }
                
                rc = pstmt.executeUpdate();
                
                if (rc > 0) {
                    counter += rc;
                }
                    
                if (total % 100000 == 0){
                    StringBuilder sb = new StringBuilder(1000);
                    sb.append("Inserting ").append(total).append("...");
                    logger.info(sb.toString());
                    conn.commit();
                }
                total++;
            }
        } catch(SQLException ex){
            Logger.getLogger(DBIdentityParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }

    /**
     * This method is the main entry point for the SAX Parser.
     * @param file the XML file to be parsed.
       */
    public void parse(String file) {
        // Use an instance of ourselves as the SAX event handler 
        DefaultHandler handler = new DBIdentityParser(conn, pstmt, logger, recordType); 
        
        // Use the default (non-validating) parser 
        SAXParserFactory factory = SAXParserFactory.newInstance(); 
        factory.setNamespaceAware(true);
        
        try {
            // Set up output stream 
            setOut(new OutputStreamWriter(System.out, "UTF8"));
            
            // Parse the input 
            SAXParser saxParser = factory.newSAXParser();
/*            
            if (saxParser.isNamespaceAware())
                System.out.println("Namespace Aware");
            else System.out.println("NOT Namespace Aware");
*/            
            // this is to handle UTF-8 data
            InputStream inputStream= new FileInputStream(file);
    	    Reader reader = new InputStreamReader(inputStream,"UTF-8");
    	    InputSource is = new InputSource(reader);
    	    is.setEncoding("UTF-8");
 
            saxParser.parse(is, handler);
        } catch (IOException ex) {
            Logger.getLogger(DBIdentityParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch (ParserConfigurationException ex) {
            Logger.getLogger(DBIdentityParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch (SAXException ex) {
            Logger.getLogger(DBIdentityParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }
}
