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
import edu.ualr.oyster.index.Index;
import edu.ualr.oyster.kb.DBEntityMap;
import edu.ualr.oyster.kb.EntityMap;
import edu.ualr.oyster.kb.ModificationRecord;
import edu.ualr.oyster.kb.TraceRecord;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.sql.SQLException;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;
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
public class IdentityParser extends OysterXMLParser {
    /** The <code>ClusterRecord</code> used during parsing */
    private ClusterRecord identity = null;
    
    /** The <code>OysterIdentityRecord</code> used during parsing */
    private OysterIdentityRecord oir = null;
    
    /**  */
    private Set<TraceRecord> traces = null;

    /**  */
    private TraceRecord tr = null;

    /** The <code>EntityMap</code> to be populated */
    private static EntityMap entityMap = null;
    
    /** The <code>Index</code> to be populated */
    private static Index valueIndex = null;
    
    /** The linkMap to be populated */
    private static HashMap<String, String> linkMap = null;
    
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
    
    // FIXME: this is a hold over from the Oyster 2.x. Do we still need it?
    /** A list of RefID's read in from the current repository */
    private static Set<String> inputIDs = null;
    
    /** The count of clusters read */
    private int count = 1;
    
    /** A list of RefID's and OysterID's read in from the current repository */
    private static HashMap<String, String> refIDLookup = null;

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
    
    private int recordType = 0;
    
    private boolean dontLoad = false;
    
    private boolean badCoDoSA = false;
    
    private boolean traceOn = false;
    
    private static Set<String> sourceNames;
    
    /**
     * Creates a new instance of <code>IdentityParser</code>.
     */
    public IdentityParser (int recordType) {
        super();
        
        this.recordType = recordType;
    }
    
    /**
     * Creates a new instance of <code>IdentityParser</code>.
     * @param index the empty index to be populated by the parser.
     * @param entity EntityMap
     * @param recordType
     */
    public IdentityParser (Index index, EntityMap entity, int recordType) {
        super();
        
        entityMap = entity;
        valueIndex = index;
        linkMap = new HashMap<String, String>();
        inputIDs = new HashSet<String>();
        refIDLookup = new HashMap<String, String>();
        mods = new TreeMap<String, ModificationRecord>();
        sourceNames = new LinkedHashSet<String>();
        
        String DATE_FORMAT = "yyyy-MM-dd";
        sdf = new java.text.SimpleDateFormat(DATE_FORMAT);
        sdf.setTimeZone(TimeZone.getDefault());
        
        this.recordType = recordType;
    }
    
    /**
     * Returns the <code>EntityMap</code> for this <code>IdentityParser</code>.
     * @return the EntityMap.
     */
    public EntityMap getEntityMap() {
        return entityMap;
    }

    /**
     * Sets the <code>EntityMap</code> for this <code>IdentityParser</code>.
     * @param aEntityMap the EntityMap to be set.
     */
    public void setEntityMap(EntityMap aEntityMap) {
        entityMap = aEntityMap;
    }

    /**
     * Returns the ValueIndex for this <code>IdentityParser</code>.
     * @return the ValueIndex.
     */
    public Index getValueIndex() {
        return valueIndex;
    }

    /**
     * Sets the ValueIndex for this <code>IdentityParser</code>.
     * @param aValueIndex the ValueIndex to be set.
     */
    public void setValueIndex(Index aValueIndex) {
        valueIndex = aValueIndex;
    }

    /**
     * Returns the LinkMap for this <code>IdentityParser</code>.
     * @return the LinkMap.
     */
    public HashMap<String, String> getLinkMap() {
        return linkMap;
    }

    /**
     * Sets the LinkMap for this <code>IdentityParser</code>.
     * @param aLinkMap the LinkMap to be set.
     */
    public void setLinkMap(HashMap<String, String> aLinkMap) {
        linkMap = aLinkMap;
    }
    
    /**
     * Returns the size of the identity repository found by this <code>IdentityParser</code>.
     * @return the size found
     */
    public int getSize(){
        return size.size();
    }
    
    /**
     * Returns a list of input ids that were read by the parser.
     * @return inputIDs
     */
    public Set<String> getInputIDs(){
        return inputIDs;
    }
    
    /**
     * Returns a look up of OysterIDs to RefIDs.
     * @return refIDLookup
     */
    public HashMap<String, String> getRefIDLookup() {
        return refIDLookup;
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

    public boolean isDontLoad() {
        return dontLoad;
    }

    public void setDontLoad(boolean dontLoad) {
        this.dontLoad = dontLoad;
    }

    public boolean isTraceOn() {
        return traceOn;
    }

    public void setTraceOn(boolean traceOn) {
        this.traceOn = traceOn;
    }
    
    public Set<String> getSourceNames() {
        return sourceNames;
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
        // build index
        System.out.println("Building Index");

        for (Iterator <String> it = entityMap.getData().keySet().iterator(); it.hasNext();){
            String key = it.next();
            ClusterRecord cr = entityMap.getCluster(key);
            
            for (int i = 0; i < cr.getSize(); i++) {
                valueIndex.addEntry(cr.getOysterIdentityRecord(i));
            }
        }
    }

    /**
     * Called when the starting of the Element is reached. For Example if we have
     * Tag called <Title> ... </Title>, then this method is called when <Title>
     * tag is Encountered while parsing the Current XML File. The attrs Parameter 
     * has the list of all Attributes declared for the Current Element in the 
     * XML File.
     * @param namespaceURI uri for this namespace
     * @param lName local xml name
     * @param qName qualified xml name
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
        } else if (eName.equalsIgnoreCase("NegStrToStr")){
            parent = eName;
        } else if (eName.equalsIgnoreCase("Value")) {
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
        } else if (eName.equalsIgnoreCase("Traces")) {
            traces = new LinkedHashSet<TraceRecord>();
        } else if (eName.equalsIgnoreCase("Trace")) {
            tr = new TraceRecord();
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
//                    System.out.println("Identifier: " + id);
                } else if(aName.equalsIgnoreCase("Name")){
                    name = token;
                } else if(aName.equalsIgnoreCase("Tag")){
                    tag = token;
                } else if(aName.equalsIgnoreCase("ID")){
                    mr.setId(token);
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
                        Logger.getLogger(IdentityParser.class.getName()).log(Level.SEVERE, null, ex);
                        
                        creationDate = now();
                    }
                    identity.setCreationDate(creationDate);
                } else if(aName.equalsIgnoreCase("OID")){
                    tr.setOid(token);
                } else if(aName.equalsIgnoreCase("RunID")){
                    tr.setRunID(token);
                } else if(aName.equalsIgnoreCase("Rule")){
                    // first remove the set notation
                    if (token.startsWith("[")) {
                        token = token.substring(1);
                    }

                    if (token.endsWith("]")) {
                        token = token.substring(0, token.length()-1);
                    }
                    
                    // now split into an arry
                    String [] temp = token.split(",");
                    
                    Set<String> set = new LinkedHashSet<String>();
                    set.addAll(Arrays.asList(temp));
                    tr.setRule(set);
                }
            }
        }
    }
    
    /**
     * Called when the Ending of the current Element is reached. For example in 
     * the above explanation, this method is called when </Title> tag is reached
     * @param namespaceURI uri for this namespace
     * @param sName
     * @param qName qualified xml name
     * @throws org.xml.sax.SAXException
     */
    @SuppressWarnings( "unchecked" )
    @Override
    public void endElement(String namespaceURI, String sName, String qName) throws org.xml.sax.SAXException {
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
        if (eName.equalsIgnoreCase("Identity")) {
            if (!badCoDoSA) {
                // HashMap<String, ClusterRecord> entityMap

                if (!isDontLoad()) {
                    if (entityMap.getClass().getSimpleName().equalsIgnoreCase("DBEntityMap")) {
                        ((DBEntityMap) entityMap).delayAddIdentity(id, identity, clusterCount);
                    } else {
                        entityMap.addIdentity(id, identity, null, null, traceOn);
                    }
                }

                for (int i = 0; i < identity.getSize(); i++) {
                    OysterIdentityRecord o = identity.getOysterIdentityRecord(i);

                    if (o.get("@RefID") != null) {
                        String refID = o.get("@RefID");
                        inputIDs.add(refID);

                        refIDLookup.put(refID, id);
                        
                        sourceNames.add((refID.split("\\."))[0]);
                    }
                }

                if (count % 10000 == 0) {
                    System.out.println("Loading " + count + "...");

                    if (entityMap.getClass().getSimpleName().equalsIgnoreCase("DBEntityMap")) {
                        try {
                            ((DBEntityMap) entityMap).getConn().commit();
                        } catch (SQLException ex) {
                            Logger.getLogger(IdentityParser.class.getName()).log(Level.SEVERE, null, ex);
                        }
                    }
                }
                count++;

                clusterCount++;
            } else {
                badCoDoSA = false;
            }
        } else if (eName.equalsIgnoreCase("Attribute")) {
            this.identity.updateMetaData(name, tag);
            name = "";
            tag = "";
        } else if (eName.equalsIgnoreCase("Reference")) {
            if (!badCoDoSA) {
                identity.insertRecord(oir);
                referenceCount++;
            }
        } else if (eName.equalsIgnoreCase("Value")) {
            String[] temp = data.trim().split("[|]");

            for (int i = 0; i < temp.length; i++) {
                String[] temp2 = temp[i].split("[\\^]");
                if (temp2.length == 2) {
                    try {
                        oir.add(identity.getAttributeNameByTag(temp2[0].trim()), temp2[1].trim());
                    } catch (NullPointerException ex) {
                        System.err.println(data);
                        Logger.getLogger(IdentityParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
                    }
                } else {
                    System.out.println("Identifier: " + id);
                    System.out.println("Bad CoDoSA OIR: " + oir);
                    System.out.println("Bad CoDoSA: " + data);
                    System.out.println("Bad CoDoSA: " + temp[i]);
                    System.out.println();

                    badCoDoSA = true;
                }
            }
            oir.setInput(true);
        } else if (eName.equalsIgnoreCase("Traces")) {
            oir.setPrevTraces(traces);
        } else if (eName.equalsIgnoreCase("Trace")) {
            traces.add(tr);
        } else if (eName.equalsIgnoreCase("Creation")) {
            mods.put(mr.getDate(), mr);
        } else if (eName.equalsIgnoreCase("Modification")) {
            mods.put(mr.getDate(), mr);
        } else if (eName.equalsIgnoreCase("OID")) {
            if (parent.equalsIgnoreCase("StrToStr")) {
                identity.getStrToStr().add(data.trim());
            } else if (parent.equalsIgnoreCase("NegStrToStr")) {
                identity.getNegStrToStr().add(data.trim());
            }
        } else if (eName.equalsIgnoreCase("StrToStr")) {
            parent = "";
        } else if (eName.equalsIgnoreCase("NegStrToStr")){
            parent = "";
        }
    }

    /**
     * This method is the main entry point for the SAX Parser.
     * @param file the XML file to be parsed.
     * @param index the empty index to be populated by the parser.
     */
    public void parse(String file, Index index, EntityMap entityMap) {
        // Use an instance of ourselves as the SAX event handler 
        DefaultHandler handler = new IdentityParser(index, entityMap, recordType); 
        
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
            Logger.getLogger(IdentityParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch (ParserConfigurationException ex) {
            Logger.getLogger(IdentityParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch (SAXException ex) {
            Logger.getLogger(IdentityParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }
}
