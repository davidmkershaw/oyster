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

import edu.ualr.oyster.ErrorFormatter;
import edu.ualr.oyster.OysterExplanationFormatter;
import edu.ualr.oyster.association.matching.OysterComparator; 
import edu.ualr.oyster.index.IndexRule;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.logging.ConsoleHandler;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Maintain the list the valid names for identity attributes
 * Responsibilities:
 * <ul>
 * <li>Access and load the text file or table containing the list valid names</li>
 * <li>Allow other objects to verify that a name is valid</li>
 * </ul>
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.19EE63FD-CEA0-2EBC-2573-D95418913D4F]
// </editor-fold> 
public class OysterAttributes {
    private String system = "";
    
    private String refID = "";
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.37EB2B0B-11D6-83FB-90ED-2EE6F1703F54]
    // </editor-fold> 
    /** The list of comparators */
    private static Map<OysterAttribute, OysterComparator> attrComp;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.BAE94A32-6FA3-8635-F21E-7EE0552F07F8]
    // </editor-fold> 
    /** The matching rules to be used for the ER run */
    private static ArrayList<OysterRule> identityRules = null;

    /** The indexing rules to be used for the ER run */
    private static ArrayList<IndexRule> indexingRules = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.9E572681-737C-B96A-64A3-62732CA0F37C]
    // </editor-fold> 
    private boolean debug = false;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.DA2319B1-609F-4E41-584A-06337EFCBAE3]
    // </editor-fold> 
    private Logger logger = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.9BDB2176-0B69-DC6F-DE2E-C19ADCFF6EEB]
    // </editor-fold> 
    private FileHandler fileHandler = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.E4CA2FD6-BB7C-57F6-C184-70D208A1813A]
    // </editor-fold> 
    private ConsoleHandler consoleHandler = null;

    /**
     * Creates a new instance of <code>OysterAttributes</code>.
     */
    public OysterAttributes () {
        attrComp = new LinkedHashMap <OysterAttribute, OysterComparator>();
        identityRules = new ArrayList<OysterRule>();
        indexingRules = new ArrayList<IndexRule>();
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.EB06E07C-D200-CA5C-4BB6-20D32C48F2D7]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>OysterAttributes</code>.
     * @param logFile
     * @param logLevel
     */
    public OysterAttributes (String logFile, Level logLevel) {
        attrComp = new LinkedHashMap <OysterAttribute, OysterComparator>();
        identityRules = new ArrayList<OysterRule>();
        indexingRules = new ArrayList<IndexRule>();
        
        try {
            // initialize logger
            logger = Logger.getLogger(getClass().getName());
            fileHandler = new FileHandler(logFile, true);
//            consoleHandler = new ConsoleHandler();
            
            // add handlers
            logger.addHandler(fileHandler);
//            logger.addHandler(consoleHandler);
            
            // set level and formatter
            logger.setLevel(logLevel);
            OysterExplanationFormatter formatter = new OysterExplanationFormatter();
            fileHandler.setFormatter(formatter);
        } catch (SecurityException ex) {
            Logger.getLogger(OysterAttributes.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch (IOException ex) {
            Logger.getLogger(OysterAttributes.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }

    /**
     * Returns the system name for this <code>OysterAttributes</code>.
     * @return the system name.
     */
    public String getSystem() {
        return system;
    }

    /**
     * Sets the system name for this <code>OysterAttributes</code>.
     * @param system the system name to be set.
     */
    public void setSystem(String system) {
        this.system = system;
    }

    /**
     * Returns the refID for this <code>OysterAttributes</code>.
     * @return the refID.
     */
    public String getRefID() {
        return refID;
    }

    /**
     * Sets the refID for this <code>OysterAttributes</code>.
     * @param refID the refID to be set.
     */
    public void setRefID(String refID) {
        this.refID = refID;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.4F611651-E90B-B94D-BA9F-BEEF479E328D]
    // </editor-fold> 
    /**
     * Returns the Attribute Comparator list for this <code>OysterAttributes</code>.
     * @return the Attribute Comparator list.
     */
    public Map <OysterAttribute, OysterComparator> getAttrComp () {
        return attrComp;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.C5248021-E769-30C0-2293-A299E04B2F57]
    // </editor-fold> 
    /**
     * Sets the Attribute Comparator list for this <code>OysterAttributes</code>.
     * @param aAttrComp the Attribute Comparator list to be set.
     */
    public void setAttrComp (Map <OysterAttribute, OysterComparator> aAttrComp) {
        attrComp = aAttrComp;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.87C29C03-01DD-FB29-F9A3-A8FE13006E90]
    // </editor-fold> 
    /**
     * Returns whether the <code>OysterAttribute</code> is contained in the <code>OysterAttributes</code>.
     * @param attribute the <code>OysterAttribute</code> to check for.
     * @return true if the <code>OysterAttribute</code> is present, otherwise false.
     */
    public boolean isOysterAttribute (OysterAttribute attribute) {
        return attrComp.containsKey(attribute);
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.F46F2748-0ED6-68CA-E0CB-0588B072AE44]
    // </editor-fold> 
    /**
     * The method returns the <code>OysterComparator</code> for this <code>OysterAttribute</code>.
     * @param attribute the <code>OysterAttribute</code> to search for.
     * @return the <code>OysterComparator</code> if present, otherwise null.
     */
    public OysterComparator getComparator (OysterAttribute attribute) {
        OysterComparator oc;
        oc = attrComp.get(attribute);
        return oc;
    }

    /**
     * The method returns the <code>OysterComparator</code> for this OysterAttribute name.
     * @param attributeName the named OysterAttribute to search for.
     * @return the <code>OysterComparator</code> if present, otherwise null.
     */
    public OysterComparator getComparator (String attributeName) {
        OysterComparator oc = null;
        for(Iterator<OysterAttribute> it = attrComp.keySet().iterator(); it.hasNext();){
            OysterAttribute oa = it.next();
            if (oa.getName().equalsIgnoreCase(attributeName)){
                oc = attrComp.get(oa);
                break;
            }
        }
        return oc;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.57315AC6-8C8B-61D7-C8AB-BEBEB8248D29]
    // </editor-fold> 
    /**
     * Returns the identity rules for this <code>OysterReferenceSource</code>.
     * @return the identity rules.
     */
    public ArrayList<OysterRule> getIdentityRules () {
        return identityRules;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.221490F0-FB30-0ADB-3E37-C10BB25D30CF]
    // </editor-fold> 
    /**
     * Sets the identity rules for this <code>OysterReferenceSource</code>.
     * @param aIdentityRules the identity rules to be set.
     */
    public void setIdentityRules (ArrayList<OysterRule> aIdentityRules) {
        identityRules = aIdentityRules;
    }
    
    /**
     * @return the indexingRules
     */
    public ArrayList<IndexRule> getIndexingRules() {
        return indexingRules;
    }

    /**
     * @param aIndexingRules the indexingRules to set
     */
    public void setIndexingRules(ArrayList<IndexRule> aIndexingRules) {
        indexingRules = aIndexingRules;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.B8952787-5B82-6D04-0052-3F1E089195B9]
    // </editor-fold> 
    /**
     * Returns whether the <code>OysterAttributes</code> is in debug mode.
     * @return true if the <code>OysterAttributes</code> is in debug mode, otherwise false.
     */
    public boolean isDebug () {
        return debug;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.1FE97CB1-A524-7E86-87BF-0BBA7C0F992B]
    // </editor-fold> 
    /**
     * Enables/disables debug mode for the <code>OysterAttributes</code>.
     * @param debug true to enable debug mode, false to disable it.
     */
    public void setDebug (boolean debug) {
        this.debug = debug;
    }

    /**
     * Adds the specified <code>OysterAttribute</code> to the HashMap, 
     * increasing its size by one.
     * @param attribute the <code>OysterAttribute</code> to be added.
     */
    public void addAttribute(OysterAttribute attribute){
        addAttribute(attribute, new OysterComparator());
    }
    
    /**
     * Adds the specified <code>OysterAttribute</code> and <code>OysterComparator</code>
     * to the HashMap, increasing its size by one.
     * @param attribute the <code>OysterAttribute</code> to be added.
     * @param comparator the <code>OysterComparator</code> to be added.
     */
    public void addAttribute(OysterAttribute attribute, OysterComparator comparator){
        attrComp.put(attribute, comparator);
    }
    
    /**
     * Adds the specified rule to the end of this ArrayList, increasing its size
     * by one.
     * @param rule the rule to be added.
     */
    public void addOysterRule(OysterRule rule){
        identityRules.add(rule);
    }
}

