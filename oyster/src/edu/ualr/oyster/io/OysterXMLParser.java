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

import java.io.IOException; 
import java.io.Writer; 
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler; 

/**
 * This is the base XML parser class from which all other XML parser will extend
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.DEDFDFD1-FA5B-462F-A625-EA18FAE25493]
// </editor-fold> 
public abstract class OysterXMLParser extends DefaultHandler {
    /** The XML data between the XML tags */
    String data = null;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.0A555965-3427-7764-838D-89159A615C7D]
    // </editor-fold> 
    /** The output Writer to use to output to stdout or a file */
    private static Writer out;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.208E1FAE-D64F-4446-F4AE-7D7D89222FBD]
    // </editor-fold> 
    /** Creates a new instance of <code>OysterXMLParser</code>. */
    public OysterXMLParser () {
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.844A7DA7-E97A-A522-0196-E7E7E4C1784D]
    // </editor-fold> 
    /**
     * Returns the Writer for this <code>OysterXMLParser</code>.
     * @return the Writer.
     */
    public Writer getOut () {
        return null;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.349334F5-CD9C-ED66-DA1E-9A7E5C32182D]
    // </editor-fold> 
    /**
     * Returns the Writer for this <code>OysterXMLParser</code>.
     * @param aOut the Writer to be set.
     */
    public void setOut (Writer aOut) {
        out = aOut;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.7A518209-A0C8-AA5C-60BE-88C4E7569187]
    // </editor-fold> 
    /**
     * Called when the Parser starts parsing the Current XML File. Handle any
     * document specific initialization code here.
     * @throws org.xml.sax.SAXException
     */
    @Override
    public abstract void startDocument () throws org.xml.sax.SAXException;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.2E7A9558-328D-9C3C-88A5-BF5D03D732CD]
    // </editor-fold> 
    /**
     * Called when the Parser Completes parsing the Current XML File. Handle any
     * document specific clean up code here.
     * @throws org.xml.sax.SAXException
     */
    @Override
    public abstract void endDocument () throws org.xml.sax.SAXException;
 
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.20D89E47-511F-7F1E-80AF-235998A0B5E5]
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
    public abstract void startElement (String namespaceURI, String lName, String qName, Attributes attrs) throws org.xml.sax.SAXException;
 
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.8A5920D9-ED12-572C-87EA-16BC0FDD60D7]
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
    public abstract void endElement (String namespaceURI, String sName, String qName) throws org.xml.sax.SAXException;
 
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.D9B3D54E-D934-2C0F-1919-A8FF3AAAA14A]
    // </editor-fold> 
    /**
     * While Parsing the XML file, if extra characters like space or enter Character
     * are encountered then this method is called. If you don't want to do anything
     * special with these characters, then you can normally leave this method blank.
     */
    @Override
    public void characters (char[] buf, int offset, int len) throws org.xml.sax.SAXException {
        String s = new String(buf, offset, len); 
        if (s.equals("&") || s.equals("\"") || s.equals("'") || s.equals("<") || s.equals(">")) {
            data += s.trim();
        } else {
            data += s.trim() + " ";
        }
    }

    /**
     * In the XML File if the parser encounters a Processing Instruction which is
     * declared like this  <?ProgramName:BooksLib QUERY="author, isbn, price"?> 
     * Then this method is called where Target parameter will have
     * "ProgramName:BooksLib" and data parameter will have  QUERY="author, isbn,
     *  price". You can invoke a External Program from this Method if required. 
     */
    @Override
    public void processingInstruction (String target, String data) throws SAXException{
    } 

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.DB675B23-8F3B-24A7-8F1D-14164E88B44D]
    // </editor-fold> 
    /**
     * Helper convenience method to output data for testing.
     * @param s the string to be output.
     * @throws org.xml.sax.SAXException
     */
    protected void emit (String s) throws org.xml.sax.SAXException {
        try { 
            out.write(s); 
            out.flush(); 
        } 
        catch (IOException e) { 
            throw new SAXException("I/O error", e); 
        } 
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.952981D5-C8C1-518C-279D-459A326D4C9B]
    // </editor-fold> 
    /**
     * Helper convenience method to output data for testing.
     * @throws org.xml.sax.SAXException
     */
    protected void nl () throws org.xml.sax.SAXException {
        String lineEnd = System.getProperty("line.separator"); 
        try { 
            out.write(lineEnd); 
        } 
        catch (IOException e) { 
            throw new SAXException("I/O error", e); 
        } 
    }

}

