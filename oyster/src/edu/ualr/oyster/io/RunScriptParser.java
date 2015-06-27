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
import edu.ualr.oyster.core.OysterRunScript; 
import java.io.File;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import org.xml.sax.Attributes; 
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

/**
 * This class is used to parse the OysterRunScript XML file and return an 
 * instantiated <code>OysterRunScript</code> object.
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.6E0A2B39-1F9A-4652-9A94-A390DE893E6A]
// </editor-fold> 
public class RunScriptParser extends OysterXMLParser {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.BB06FE95-AE94-BA7D-E237-96CF9FAC3139]
    // </editor-fold> 
    /** The <code>OysterRunScript</code> to be populated */
    private static OysterRunScript runScript;// = new OysterRunScript();
    
    /** Used to hold the current XML parent tag */
    private String parent = "";
    
    /** The LCRD filter used during parsing */
    private ArrayList<String> filter = null;

    /** The filterNumber used during parsing */
    private int filterNumber = 1;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.AAAAC5A5-AA73-F505-6B15-35C39FEA65D2]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>RunScriptParser</code>.
     */
    public RunScriptParser () {
        super();
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.68381C37-A0DA-48BF-7455-2226B713C8C3]
    // </editor-fold> 
    /**
     * Returns the <code>OysterRunScript</code> for this <code>RunScriptParser</code>.
     * @return the <code>OysterRunScript</code>.
     */
    public OysterRunScript getRunScript () {
        return runScript;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.7BFAB102-7817-831E-CA70-E701F850FD55]
    // </editor-fold> 
    /**
     * Sets the <code>OysterRunScript</code> for this <code>RunScriptParser</code>.
     * @param rs the <code>OysterRunScript</code> to be set.
     */
    public void setRunScript (OysterRunScript rs) {
        runScript = rs;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.BDD384C3-44E8-A45F-88C7-153F39CBCD20]
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
    // #[regen=yes,id=DCE.DB4AA7BC-6769-55CE-1027-6C6C3DE5F115]
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
    // #[regen=yes,id=DCE.84B81869-DD2A-A6E0-0FC7-F34BC0BDA3EB]
    // </editor-fold> 
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
    public void startElement(String namespaceURI, String lName, String qName, Attributes attrs) throws org.xml.sax.SAXException {
        String eName = lName; // element name
        if ("".equals(eName)) {
            eName = qName;
        }
        // namespaceAware = false emit("<"+eName);

        // clear the data
        data = "";

        if (eName.equalsIgnoreCase("Settings")) {
            parent = eName;
        } else if (eName.equalsIgnoreCase("AttributePath")) {
            
        } else if (eName.equalsIgnoreCase("IdentityInput")) {
            parent = eName;
        } else if (eName.equalsIgnoreCase("IdentityOutput")) {
            parent = eName;
        } else if (eName.equalsIgnoreCase("LinkOutput")) {
            parent = eName;
        } else if (eName.equalsIgnoreCase("ReferenceSources")) {
            runScript.setSources(new HashSet<String>());
        } else if (eName.equalsIgnoreCase("Source")) {
            
        } else if (eName.equalsIgnoreCase("EREngine")) {
            parent = eName;
        } else if (eName.equalsIgnoreCase("IDGenerator")) {
            parent = eName;
        } else if (eName.equalsIgnoreCase("LCRD")) {
            runScript.setLcrd(new LinkedHashMap<Integer, ArrayList<String>>());
            parent = eName;
        } else if (eName.equalsIgnoreCase("Filter")) {
            filter = new ArrayList<String>();
            parent = eName;
        } else if (eName.equalsIgnoreCase("Index")) {
            parent = eName;
        } else if (eName.equalsIgnoreCase("GC")) {
            parent = eName;
        } else if (eName.equalsIgnoreCase("EntityMap")) {
            parent = eName;
        } else if (eName.equalsIgnoreCase("SlidingWindow")) {
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

                if (aName.equalsIgnoreCase("RunScriptName")) {
                    runScript.setName(token);
                } else if (aName.equalsIgnoreCase("Explanation")) {
                    if (token.equalsIgnoreCase("On")) {
                        runScript.setExplanation(true);
                    } else {
                        runScript.setExplanation(false);
                    }
                } else if (aName.equalsIgnoreCase("Debug")) {
                    if (token.equalsIgnoreCase("On")) {
                        runScript.setDebug(true);
                    } else {
                        runScript.setDebug(false);
                    }
                } else if (aName.equalsIgnoreCase("SS")) {
                    if (token.equalsIgnoreCase("On")) {
                        runScript.setSystemStats(true);
                    } else {
                        runScript.setSystemStats(false);
                    }
                } else if (aName.equalsIgnoreCase("ChangeReportDetail")) {
                    if (token.equalsIgnoreCase("Yes")) {
                        runScript.setChangeReportDetail(true);
                    } else {
                        runScript.setChangeReportDetail(false);
                    }
                } else if (aName.equalsIgnoreCase("Type")) {
                    if (parent.equalsIgnoreCase("IdentityInput")) {
                        runScript.setIdentityInputType(token);
                    } else if (parent.equalsIgnoreCase("IdentityOutput")) {
                        runScript.setIdentityOutputType(token);
                    } else if (parent.equalsIgnoreCase("LinkOutput")) {
                        runScript.setLinkOutputType(token);
                    } else if (parent.equalsIgnoreCase("EREngine")) {
                        runScript.setEngineType(token);
                    } else if (parent.equalsIgnoreCase("EntityMap")) {
                        runScript.setEntityMapType(token);
                    }
                } else if (aName.equalsIgnoreCase("Server")) {
                    if (parent.equalsIgnoreCase("IdentityInput")) {
                        runScript.setIdentityInputServer(token);
                    } else if (parent.equalsIgnoreCase("IdentityOutput")) {
                        runScript.setIdentityOutputServer(token);
                    } else if (parent.equalsIgnoreCase("LinkOutput")) {
                        runScript.setLinkOutputServer(token);
                    } else if (parent.equalsIgnoreCase("EntityMap")) {
                        runScript.setEntityMapServer(token);
                    }
                } else if (aName.equalsIgnoreCase("Port")) {
                    if (parent.equalsIgnoreCase("IdentityInput")) {
                        runScript.setIdentityInputPort(token);
                    } else if (parent.equalsIgnoreCase("IdentityOutput")) {
                        runScript.setIdentityOutputPort(token);
                    } else if (parent.equalsIgnoreCase("LinkOutput")) {
                        runScript.setLinkOutputPort(token);
                    } else if (parent.equalsIgnoreCase("EntityMap")) {
                        runScript.setEntityMapPort(token);
                    }
                } else if (aName.equalsIgnoreCase("SID")) {
                    if (parent.equalsIgnoreCase("IdentityInput")) {
                        runScript.setIdentityInputSID(token);
                    } else if (parent.equalsIgnoreCase("IdentityOutput")) {
                        runScript.setIdentityOutputSID(token);
                    } else if (parent.equalsIgnoreCase("LinkOutput")) {
                        runScript.setLinkOutputSID(token);
                    } else if (parent.equalsIgnoreCase("EntityMap")) {
                        runScript.setEntityMapSID(token);
                    }
                } else if (aName.equalsIgnoreCase("UserID")) {
                    if (parent.equalsIgnoreCase("IdentityInput")) {
                        runScript.setIdentityInputUserID(token);
                    } else if (parent.equalsIgnoreCase("IdentityOutput")) {
                        runScript.setIdentityOutputUserID(token);
                    } else if (parent.equalsIgnoreCase("LinkOutput")) {
                        runScript.setLinkOutputUserID(token);
                    } else if (parent.equalsIgnoreCase("EntityMap")) {
                        runScript.setEntityMapUserID(token);
                    }
                } else if (aName.equalsIgnoreCase("Passwd")) {
                    if (parent.equalsIgnoreCase("IdentityInput")) {
                        runScript.setIdentityInputPasswd(token);
                    } else if (parent.equalsIgnoreCase("IdentityOutput")) {
                        runScript.setIdentityOutputPasswd(token);
                    } else if (parent.equalsIgnoreCase("LinkOutput")) {
                        runScript.setLinkOutputPasswd(token);
                    } else if (parent.equalsIgnoreCase("EntityMap")) {
                        runScript.setEntityMapPasswd(token);
                    }
                } else if (aName.equalsIgnoreCase("CType")) {
                    if (parent.equalsIgnoreCase("IdentityInput")) {
                        
                    } else if (parent.equalsIgnoreCase("IdentityOutput")) {
                        
                    } else if (parent.equalsIgnoreCase("LinkOutput")) {
                        
                    } else if (parent.equalsIgnoreCase("EntityMap")) {
                        runScript.setEntityMapCType(token);
                    }
                } else if (aName.equalsIgnoreCase("Num")) {
                    runScript.setLogFileNum(Integer.parseInt(token));
                } else if (aName.equalsIgnoreCase("Size")) {
                    runScript.setLogFileSize(Integer.parseInt(token));
                } else if (aName.equalsIgnoreCase("SecurityHash")) {
                    runScript.setSecurityHash(token);
                } else if (parent.equalsIgnoreCase("LCRD") && aName.equalsIgnoreCase("ByPass")) {
                    if (token.equalsIgnoreCase("Yes")) {
                        runScript.setBypassFilter(true);
                    } else {
                        runScript.setBypassFilter(false);
                    }
                } else if (aName.equalsIgnoreCase("PreLoad")) {
                    if (token.equalsIgnoreCase("Yes")) {
                        runScript.setPreLoad(true);
                    } else {
                        runScript.setPreLoad(false);
                    }
                } else if (aName.equalsIgnoreCase("Size")) {
                    if (parent.equalsIgnoreCase("SlidingWindow")) {
                        runScript.setSlidingWindow(Integer.parseInt(token));
                    }
                } else if (aName.equalsIgnoreCase("Trace")) {
                    if (token.equalsIgnoreCase("On")) {
                        runScript.setIdentityOutputTrace(true);
                    } else {
                        runScript.setIdentityOutputTrace(false);
                    }
                }
            }
        }
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.BDA83A51-4C31-63F2-7785-FFD067240C3B]
    // </editor-fold> 
    /**
     * Called when the Ending of the current Element is reached. For example in 
     * the above explanation, this method is called when </Title> tag is reached
     * @param namespaceURI URI for this namespace
     * @param sName
     * @param qName qualified XML name
     * @throws org.xml.sax.SAXException
     */
    @Override
    public void endElement (String namespaceURI, String sName, String qName) throws org.xml.sax.SAXException {
        String eName = sName; // element name 
        if ("".equals(eName)) {
            eName = qName;
        }
        
        if (eName.equalsIgnoreCase("OysterRunScript")){
            runScript = new OysterRunScript();
        } else if (eName.equalsIgnoreCase("Settings")){
            parent = "";
        } else if (eName.equalsIgnoreCase("AttributePath")){
            runScript.setAttributeLocation(data.trim());
        } else if (eName.equalsIgnoreCase("IdentityInput")){
            runScript.setIdentityInputLocation(data.trim());
            parent = "";
        } else if (eName.equalsIgnoreCase("IdentityOutput")){
            runScript.setIdentityOutputLocation(data.trim());
            parent = "";
        } else if (eName.equalsIgnoreCase("LinkOutput")){
            runScript.setLinkOutputLocation(data.trim());
            parent = "";
        } else if (eName.equalsIgnoreCase("ReferenceSources")){
            
        } else if (eName.equalsIgnoreCase("LogFile")){
            runScript.setLogFile(data.trim());
        } else if (eName.equalsIgnoreCase("Source")){
            runScript.getSources().add(data.trim());
        } else if (eName.equalsIgnoreCase("EREngine")){
            parent = "";
        } else if (eName.equalsIgnoreCase("IDGenerator")){
            parent = "";
        } else if (eName.equalsIgnoreCase("Element")){
            filter.add(data.trim());
            parent = "";
        } else if (eName.equalsIgnoreCase("Filter")){
            runScript.getLcrd().put(filterNumber, filter);
            filterNumber++;
            parent = "";
        } else if (eName.equalsIgnoreCase("GC")){
            runScript.setGc(Integer.parseInt(data.trim()));
            parent = "";
        } else if (eName.equalsIgnoreCase("RunMode")){
            runScript.setRunMode(data.trim());
        } else if (eName.equalsIgnoreCase("AssertionInput")){
            runScript.setAssertionInputLocation(data.trim());
        } else if (eName.equalsIgnoreCase("SlidingWindow")){
            parent = "";
        }
    }
    
    /**
     * This method is the main entry point for the SAX Parser.
     * @param file the XML file to be parsed.
     * @return <code>OysterRunScript</code> containing data from the file.
     */
    public OysterRunScript parse(String file){
        // Use an instance of ourselves as the SAX event handler 
        DefaultHandler handler = new RunScriptParser(); 
        // Use the default (non-validating) parser 
        SAXParserFactory factory = SAXParserFactory.newInstance(); 
        factory.setNamespaceAware(true);
        
        try {
            // Set up output stream 
            setOut(new OutputStreamWriter(System.out, "UTF8"));
            runScript = new OysterRunScript();
            
            // Parse the input 
            SAXParser saxParser = factory.newSAXParser();
/*            
            if (saxParser.isNamespaceAware())
                System.out.println("Namespace Aware");
            else System.out.println("NOT Namespace Aware");
*/            
            saxParser.parse( new File(file), handler);
        } catch (IOException ex) {
            Logger.getLogger(RunScriptParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
            System.err.println(file);
        } catch (ParserConfigurationException ex) {
            Logger.getLogger(RunScriptParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
            System.err.println(file);
        } catch (SAXException ex) {
            Logger.getLogger(RunScriptParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
            System.err.println(file);
        }
        
        return runScript;
    }
    
    // FIXME: Need to add Parser Level and XML Level validation
}

