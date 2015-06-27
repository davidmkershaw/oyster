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

import edu.ualr.oyster.utilities.OysterEditDistance;
import edu.ualr.oyster.utilities.OysterNickNameTable;
import edu.ualr.oyster.utilities.OysterUtilityTranspose;
import java.util.Locale;

/**
 * Name Comparator class can be used with First, Middle and Last names.
 *
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.5FF104D8-BC66-6819-B55A-07F4976B16DE]
// </editor-fold> 
public class OysterNameComparator extends OysterComparator {
    /** Nickname/Alias lookup */
    private OysterNickNameTable nnTable;
    
    /** Single character transposition operator */
    private OysterUtilityTranspose transpose;
    
    /** Levenshtein Edit Distance */
    private OysterEditDistance editDist;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.E3EF23FE-0550-8390-6C9B-A8C6A23F6489]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>OysterNameComparator</code>.
     */
    public OysterNameComparator () {
        super();
        
        String [] arr = {"INITIAL","NICKNAME","TRANSPOSE","LED80"};
        for (int i = 0; i < arr.length; i++){
            matchCodes.add(arr[i]);
            matchCodes.add("~"+arr[i]);
        }
        
        transpose = new OysterUtilityTranspose();
        nnTable = new OysterNickNameTable();
        editDist = new OysterEditDistance();
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.E9642B46-C38F-7C30-0C0F-670059FD541F]
    // </editor-fold> 
    /**
     * Returns the match code for this <code>OysterNameComparator</code>.
     * @param s source String.
     * @param t target String.
     * @param matchType the type of match to preform.
     * @return "Initial", "Nickname", "Transpose", "Led80" or "X".
     */
    @Override
    public String getMatchCode (String s, String t, String matchType) {
        String result, tempMatchType = matchType;
        int sLen = s.length();
        int tLen = t.length();
        boolean not = false;
        
        // Check for NOT operator
        if (matchType.toUpperCase(Locale.US).startsWith("~")){
            matchType = matchType.substring(1);
            not = true;
        }
        
        //======================================================================
        //======================================================================
        if (!not) {
            if (matchType.equalsIgnoreCase("Initial") && (s.charAt(0) == t.charAt(0)
                    && ((sLen == 1 && tLen > 1) || (sLen > 1 && tLen == 1)))) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("NickName") && nnTable.isNicknamePair(s, t)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("Transpose") && transpose.differByTranspose(s, t)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("Led80")) {
            // calculate edit distance
            editDist.computeDistance(s, t);
            
            // if greater than or equal to normalized score it's a match
            if (editDist.computeNormalizedScore() >= 0.8) {
                result = tempMatchType;
            } else {
                result = "X";
            }
        } else {
            result = "X";
        }
        } else {
            if (matchType.equalsIgnoreCase("Initial") && !(s.charAt(0) == t.charAt(0)
                    && ((sLen == 1 && tLen > 1) || (sLen > 1 && tLen == 1)))) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("NickName") && !nnTable.isNicknamePair(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("Transpose") && !transpose.differByTranspose(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("Led80")) {
                // calculate edit distance
                editDist.computeDistance(s, t);

                // if greater than or equal to normalized score it's a match
                if (!(editDist.computeNormalizedScore() >= 0.8)) {
                    result = tempMatchType;
                } else {
                    result = "X";
                }
            } else {
                result = "X";
            }
        }
        
        return result.toUpperCase();
    }
}
