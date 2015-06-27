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
import edu.ualr.oyster.core.OysterReferenceSource; 
import edu.ualr.oyster.core.ReferenceItem;
import java.io.File;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import org.xml.sax.Attributes; 
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

/**
 * This class is used to parse the OysterSourceDescriptor XML file and return an 
 * instantiated <code>OysterReferenceSource</code> object.
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.0820CA6C-10E9-29D7-2A13-FE967598313D]
// </editor-fold> 
public class SourceDescriptorParser extends OysterXMLParser {
    /** The <code>OysterReferenceSource</code> to be populated */
    OysterReferenceSource sourceDescriptor = null;
    
    /** The items used during parsing */
    ArrayList<ReferenceItem> items = null;
    
    /** The <code>ReferenceItem</code> used during parsing */
    ReferenceItem referenceItem = null;
    
    /** Used to hold the current XML parent tag */
    private String parent = "";
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.A8B7A4FA-2CED-C481-5B93-461AF28B68E8]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>SourceDescriptorParser</code>.
     */
    public SourceDescriptorParser () {
        sourceDescriptor = new OysterReferenceSource();
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.88946911-9261-9825-0C08-2E388F0A095A]
    // </editor-fold> 
    /**
     * Called when the Parser starts parsing the Current XML File. Handle any
     * document specific initialization code here.
     * @throws org.xml.sax.SAXException
     */
    @Override
    public void startDocument () throws org.xml.sax.SAXException {
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.3D477272-622B-EBE3-659B-EEFB7C5BA169]
    // </editor-fold> 
    /**
     * Called when the Parser Completes parsing the Current XML File. Handle any
     * document specific clean up code here.
     * @throws org.xml.sax.SAXException
     */
    @Override
    public void endDocument () throws org.xml.sax.SAXException {
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.08A0325B-4E6B-60D8-5F57-5FF17EDC96D3]
    // </editor-fold> 
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
    public void startElement(String namespaceURI, String lName, String qName, Attributes attrs) throws org.xml.sax.SAXException {
        String eName = lName; // element name 
        if ("".equals(eName)) {
            eName = qName;
        }

        // clear the data
        data = "";

        if (eName.equalsIgnoreCase("OysterSourceDescriptor")) {
            sourceDescriptor = new OysterReferenceSource();
            parent = eName;
        } else if (eName.equalsIgnoreCase("ReferenceItems")) {
            items = new ArrayList<ReferenceItem>();
        } else if (eName.equalsIgnoreCase("Item")) {
            referenceItem = new ReferenceItem();
            parent = eName;
        } else if (eName.equalsIgnoreCase("Term")) {
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

                if (aName.equalsIgnoreCase("Name")) {
                    if (parent.equalsIgnoreCase("OysterSourceDescriptor")) {
                        sourceDescriptor.setSourceName(token);
                    } else if (parent.equalsIgnoreCase("Item")) {
                        referenceItem.setName(token);
                    }
                } else if (aName.equalsIgnoreCase("Type")) {
                    sourceDescriptor.setSourceType(token);
                } else if (aName.equalsIgnoreCase("Char")) {
                    sourceDescriptor.setDelimiter(token);
                } else if (aName.equalsIgnoreCase("Qual")) {
                    if (token.equals("\"") || token.equals("'")) {
                        sourceDescriptor.setQualifer(token);
                    } else if (!token.equals("")) {
                        StringBuilder sb = new StringBuilder(1000);
                        sb.append("##Error: ").append(token).append(" is not an approved qualifer.");
                        Logger.getLogger(SourceDescriptorParser.class.getName()).
                                log(Level.SEVERE, sb.toString());
                    } else {
                        sourceDescriptor.setQualifer("");
                    }
                } else if (aName.equalsIgnoreCase("Labels")) {
                    if (token.equalsIgnoreCase("Y")) {
                        sourceDescriptor.setLabel(true);
                    } else {
                        sourceDescriptor.setLabel(false);
                    }
                } else if (aName.equalsIgnoreCase("Server")) {
                    sourceDescriptor.setServer(token);
                } else if (aName.equalsIgnoreCase("Port")) {
                    sourceDescriptor.setPort(token);
                } else if (aName.equalsIgnoreCase("SID")) {
                    sourceDescriptor.setSid(token);
                } else if (aName.equalsIgnoreCase("UserID")) {
                    sourceDescriptor.setUserID(token);
                } else if (aName.equalsIgnoreCase("Passwd")) {
                    sourceDescriptor.setPasswd(token);
                } else if (aName.equalsIgnoreCase("CType")) {
                    sourceDescriptor.setConnectionType(token);
                } else if (aName.equalsIgnoreCase("Attribute")) {
                    referenceItem.setAttribute(token);
                } else if (aName.equalsIgnoreCase("Format")) {
                    referenceItem.setFormat(token);
                } else if (aName.equalsIgnoreCase("FormatType")) {
                    referenceItem.setFormatType(token);
                } else if (aName.equalsIgnoreCase("Pos")) {
                    referenceItem.setOrdinal(Integer.parseInt(token));
                } else if (aName.equalsIgnoreCase("Start")) {
                    referenceItem.setStart(Integer.parseInt(token));
                } else if (aName.equalsIgnoreCase("End")) {
                    referenceItem.setEnd(Integer.parseInt(token));
                }
            }
        }
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.7CF14671-F737-C02C-20A2-3C30C3A03770]
    // </editor-fold> 
    /**
     * Called when the Ending of the current Element is reached. For example in 
     * the above explanation, this method is called when </Title> tag is reached
     * @param namespaceURI uri for this namespace
     * @param sName
     * @param qName qualified xml name
     * @throws org.xml.sax.SAXException
     */
    @Override
    public void endElement (String namespaceURI, String sName, String qName) throws org.xml.sax.SAXException {
        String eName = sName; // element name 
        if ("".equals(eName)) {
            eName = qName;
        } 
        
        if (eName.equalsIgnoreCase("OysterSourceDescriptor")){
        } else if (eName.equalsIgnoreCase("Source")){
            sourceDescriptor.setSourcePath(data.trim());
        } else if (eName.equalsIgnoreCase("ReferenceItems")){
            sourceDescriptor.setReferenceItems(items);
        } else if (eName.equalsIgnoreCase("Item")){
            items.add(referenceItem);
            parent = "";
        } else if (eName.equalsIgnoreCase("OverRideSQL")){
            sourceDescriptor.setOverRideSQL(data.trim());
        }
    }
    
    /**
     * This method is the main entry point for the SAX Parser.
     * @param file the XML file to be parsed.
     * @return <code>OysterReferenceSource</code> containing data from the file.
     */
    public OysterReferenceSource parse(String file){
        // Use an instance of ourselves as the SAX event handler 
        DefaultHandler handler = new SourceDescriptorParser(); 
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
            saxParser.parse( new File(file), handler);
        } catch (IOException ex) {
            Logger.getLogger(SourceDescriptorParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch (ParserConfigurationException ex) {
            Logger.getLogger(SourceDescriptorParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch (SAXException ex) {
            Logger.getLogger(SourceDescriptorParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        
        return sourceDescriptor;
    }
    
    // FIXME: Need to add Parser Level and XML Level validation
    // i.e. if source is of type database attributes must be Name and Attribute only
}

