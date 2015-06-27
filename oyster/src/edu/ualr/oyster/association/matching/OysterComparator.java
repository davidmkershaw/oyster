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

package edu.ualr.oyster.association.matching;

import java.util.ArrayList;
import java.util.Locale;

/**
 * This is the base comparator class from which all other comparator class should
 * extend from. 
 * 
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker ">
// #[regen=yes,id=DCE.1B181697-9054-D93E-540D-F1F60C1F699B]
// </editor-fold>
public class OysterComparator {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.FA2182B8-B356-A517-70CB-BCFD5235F030]
    // </editor-fold>
    /** */
    protected boolean debug = false;

    /** Holds the matchCodes for the comparator */
    protected ArrayList<String> matchCodes;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.0A6BA72D-D143-E774-D41A-F5F28477E67F]
    // </editor-fold>
    /**
     * Creates a new instance of <code>OysterComparator</code>.
     */
    public OysterComparator () {
        matchCodes = new ArrayList<String>();
        String [] arr = {"EXACT", "EXACT_IGNORE_CASE","MISSING"};
        for (int i = 0; i < arr.length; i++){
            matchCodes.add(arr[i]);
            matchCodes.add("~"+arr[i]);
        }
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.896A3F63-5432-B560-C169-F49EDF2BBC40]
    // </editor-fold>
    /**
     * Returns whether the <code>OysterComparator</code> is in debug mode.
     * @return true if the <code>OysterComparator</code> is in debug mode, otherwise false.
     */
    public boolean isDebug () {
        return debug;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.E20F80AB-B014-ECBD-09AB-BF9BF19EC2DC]
    // </editor-fold>
    /**
     * Enables/disables debug mode for the <code>OysterComparator</code>.
     * @param debug true to enable debug mode, false to disable it.
     */
    public void setDebug (boolean debug) {
        this.debug = debug;
    }

    /**
     * Returns whether the match code is a valid match code for this <code>OysterComparator</code>.
     * @param s match code to be checked.
     * @return true if the <code>OysterComparator</code> is in debug mode, otherwise false.
     */
    public boolean isMatchCode(String s){
        // FIXME: Need to add a resource bundle for Locale oriented data
        return matchCodes.contains(s.toUpperCase(Locale.US));
    }
    
    /**
     * This method compares the source string to the target string based on this 
     * Comparators comparison parameters. If a comparison is found will return
     * the appropriate match code string.
     * @param s source String.
     * @param t target String.
     * @param matchType the type of match to preform.
     * @return the match code found.
     */
    public String compare (String s, String t, String matchType) {
        String result, tempMatchType = matchType;
        boolean not = false;
        
        // Check for NOT operator
        if (matchType.toUpperCase(Locale.US).startsWith("~")){
            matchType = matchType.substring(1);
            not = true;
        }
        
        //======================================================================
        //======================================================================
        if (!not) {
            if (matchType.equalsIgnoreCase("Missing") && !(s == null || (s.trim()).isEmpty())) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("Missing") && !(t == null || (t.trim()).isEmpty())) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("Exact") && (s.equals(t)
                    && s != null && !(s.trim()).isEmpty()
                    && t != null && !(t.trim()).isEmpty())) {
                result =  tempMatchType;
            } else if (matchType.equalsIgnoreCase("Exact_Ignore_Case") && (s.equalsIgnoreCase(t)
                    && s != null && !(s.trim()).isEmpty()
                    && t != null && !(t.trim()).isEmpty())) {
                result =  tempMatchType;
            } else {
                result = getMatchCode(s, t, tempMatchType);
            }
        } else {
            if (matchType.equalsIgnoreCase("Missing") && !(s == null || (s.trim()).isEmpty())) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("Missing") && !(t == null || (t.trim()).isEmpty())) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("Exact") && !(s.equals(t)
                    && s != null && !(s.trim()).isEmpty()
                    && t != null && !(t.trim()).isEmpty())) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("Exact_Ignore_Case") && !(s.equalsIgnoreCase(t)
                    && s != null && !(s.trim()).isEmpty()
                    && t != null && !(t.trim()).isEmpty())) {
                result = tempMatchType;
            } else {
                result = getMatchCode(s, t, tempMatchType);
            }
        }
        return result.toUpperCase();
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker ">
    // #[regen=yes,id=DCE.A95127E9-089A-E66D-2D1B-14EF3F4B8185]
    // </editor-fold>
    /**
     * Returns the match code for this <code>OysterComparator</code>.
     * @param s source String.
     * @param t target String.
     * @param matchType the type of match to preform.
     * @return the match code.
     */
    public String getMatchCode (String s, String t, String matchType) {
        return "X";
    }
    
    public final String getAllAvailableMatchCodes(){
        StringBuilder sb = new StringBuilder();
        sb.append(getClass().getName());
        sb.append(matchCodes);
        return sb.toString();
    }
    
    @Override
    /**
     * Returns a String representation of the <code>OysterComparator</code> object
     * @return a String
     */
    public String toString(){
        StringBuilder sb = new StringBuilder();
        sb.append(getClass().getName());
        
        return sb.toString();
    }
}

