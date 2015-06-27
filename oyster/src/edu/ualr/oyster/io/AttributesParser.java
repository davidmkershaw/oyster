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
import edu.ualr.oyster.core.OysterAttribute;
import edu.ualr.oyster.core.OysterAttributes; 
import edu.ualr.oyster.core.OysterRule;
import edu.ualr.oyster.core.RuleTerm;
import edu.ualr.oyster.index.IndexRule;
import java.io.File;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import org.xml.sax.Attributes; 
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

/**
 * This class is used to parse the OysterAttribute XML file and return an 
 * instantiated <code>OysterAttributes</code> object.
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.6F28B8D9-3183-A5B9-64FA-84BBBADB209B]
// </editor-fold> 
public class AttributesParser extends OysterXMLParser {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.8E44A93B-3348-14AC-8CBF-D6A11FCD9AFE]
    // </editor-fold> 
    /** The <code>OysterAttributes</code> to be populated */
    private OysterAttributes attributes = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.50D59AEA-8D26-C8A8-0E7A-6D2884FC53DB]
    // </editor-fold> 
    /** The <code>OysterAttribute</code> used during parsing */
    private OysterAttribute attribute = null;
    
    /** The identityRules used during parsing */
    ArrayList<OysterRule> identityRules = null;
    
    /** The <code>OysterRule</code> used during parsing */
    OysterRule rule = null;
    
    /** The termItem used during parsing */
    String termItem = null;
    
    /** The termItem used during parsing */
    Set<String> compareTo = null;
    
    /** The matchResult used during parsing */
    String matchResult = null;
    
    /** The indexingRules used during parsing */
    ArrayList<IndexRule> indexingRules = null;
    
    /** The <code>OysterRule</code> used during parsing */
    IndexRule indexRule = null;
    
    /** The Indexing Rule Item used during parsing */
    String ruleItem = null;
    
    /** The Indexing Rule Hash used during parsing */
    String hash = null;
    
    /** Used to hold the current XML parent tag */
    private String parent = "";
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.371E32D5-044D-C241-DE2F-9814B0A4CBC0]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>AttributesParser</code>.
     */
    public AttributesParser () {
        super();
        attributes = new OysterAttributes();
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.03CD2D42-6217-96C4-60F9-0C12CC3E0DAD]
    // </editor-fold> 
    /**
     * Returns the <code>OysterAttributes</code> for this <code>AttributesParser</code>.
     * @return the <code>OysterAttributes</code>.
     */
    public OysterAttributes getAttributes () {
        return attributes;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.5053D36C-3EE6-1761-12F7-0C32E031F20A]
    // </editor-fold> 
    /**
     * Sets the <code>OysterAttributes</code> for this <code>AttributesParser</code>.
     * @param attributes the <code>OysterAttributes</code> to be set.
     */
    public void setAttributes (OysterAttributes attributes) {
        this.attributes = attributes;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.B7C13113-D026-4F51-2FB8-496E3F28524C]
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
    // #[regen=yes,id=DCE.D6E36BC6-859C-DE45-B93A-D681C2579428]
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
    // #[regen=yes,id=DCE.613C125B-B393-3EE4-544C-5436FB1863F9]
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
    public void startElement (String namespaceURI, String lName, String qName, Attributes attrs) throws org.xml.sax.SAXException {
        String eName = lName; // element name
        if ("".equals(eName)) {
            eName = qName;
        }
        // namespaceAware = false emit("<"+eName);
        
        // clear the data
        data = "";
        
        if (eName.equalsIgnoreCase("OysterAttributes")){
            parent = eName;
        } else if (eName.equalsIgnoreCase("Attribute")){
            attribute = new OysterAttribute();
            parent = eName;
        } else if (eName.equalsIgnoreCase("IdentityRules")){
            identityRules = new ArrayList<OysterRule>();
        } else if (eName.equalsIgnoreCase("Indices")){
            indexingRules = new ArrayList<IndexRule>();
        } else if (eName.equalsIgnoreCase("Rule")){
            rule = new OysterRule();
            parent = eName;
        } else if (eName.equalsIgnoreCase("Term")){
            parent = eName;
        } else if (eName.equalsIgnoreCase("Index")){
            indexRule = new IndexRule();
            parent = eName;
        } else if (eName.equalsIgnoreCase("Segment")){
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
                
                if(aName.equalsIgnoreCase("System")){
                    attributes.setSystem(token);
                }
/*                
                else if(aName.equalsIgnoreCase("RefID")){
                    attributes.setRefID(token);
                }
*/ 
                else if(aName.equalsIgnoreCase("Item")){
                    if (parent.equalsIgnoreCase("Attribute")){
                        attribute.setName(token);
                        // prep so that no nulls exist for any item that is set.
                        attribute.setAlgorithm("");
                    } else if (parent.equalsIgnoreCase("Term")){
                        termItem = token;
                    } else if (parent.equalsIgnoreCase("Segment")){
                        ruleItem = token;
                    }
                } else if(aName.equalsIgnoreCase("CompareTo")){
                    compareTo = new HashSet<String>();
                    String [] temp = token.split("[;]");
                    compareTo.addAll(Arrays.asList(temp));
                } else if(aName.equalsIgnoreCase("Algo")){
                    attribute.setAlgorithm(token);
                } else if(aName.equalsIgnoreCase("Ident")){
                    if (parent.equalsIgnoreCase("Rule")) {
                    rule.setRuleIdentifer(token);
                    } else if (parent.equalsIgnoreCase("Index")) {
                        indexRule.setRuleIdentifier(token);
                    }
                } else if(aName.equalsIgnoreCase("MatchResult")){
                    matchResult = token;
                } else if(aName.equalsIgnoreCase("Hash")){
                    hash = token;
                }
            }
        }
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.BF9EB3BB-87CB-F091-2B67-5F5E92534788]
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
        
        if (eName.equalsIgnoreCase("Attribute")){
            attributes.addAttribute(attribute);
            parent = "";
        } else if (eName.equalsIgnoreCase("IdentityRules")){
            attributes.setIdentityRules(identityRules);
        } else if (eName.equalsIgnoreCase("Rule")){
            this.identityRules.add(rule);
        } else if (eName.equalsIgnoreCase("Term")){
            RuleTerm rt = new RuleTerm();
            rt.setItem(termItem);
            rt.setCompareTo(compareTo);
            rt.setMatchResult(matchResult);

            rule.getTermList().add(rt);
            parent = "";
            compareTo = null;
        } else if (eName.equalsIgnoreCase("Indices")){
            attributes.setIndexingRules(indexingRules);
        } else if (eName.equalsIgnoreCase("Index")){
            this.indexingRules.add(indexRule);
        } else if (eName.equalsIgnoreCase("Segment")){
            indexRule.getSegments().put(ruleItem, hash);
            parent = "";
        }
    }
    
    /**
     * This method is the main entry point for the SAX Parser.
     * @param file the XML file to be parsed.
     * @return <code>OysterAttributes</code> containing data from the file.
     */
    public OysterAttributes parse(String file){
        // Use an instance of ourselves as the SAX event handler 
        DefaultHandler handler = new AttributesParser(); 
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
            Logger.getLogger(AttributesParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch (ParserConfigurationException ex) {
            Logger.getLogger(AttributesParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch (SAXException ex) {
            Logger.getLogger(AttributesParser.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return attributes;
    }
    
    // FIXME: Need to add Parser Level and XML Level validation
}

