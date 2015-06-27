/*
 * Copyright 2012 John Talburt, Eric Nelson
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

import edu.ualr.oyster.utilities.CharacterSubstringMatches;
import edu.ualr.oyster.utilities.OysterEditDistance;
import edu.ualr.oyster.utilities.OysterUtilityTranspose;
import java.util.Locale;

/**
 * Match Codes
 * True/False Matchcodes - these either match "equivalently" or they don't
 * 1. PHONEMATCH - a source and target are the same phone number if all non-digit
 * characters are removed.
 *  <b>
 * 2. TRANSPOSE – a source and target are equivalent if there have at most one 
 * adjacent char that are swapped. i.e. John ≈ Jonh.<b>
 *  <b>
 *  <b>
 *  <b>
 * Functionalized – these must met some threshold to be considered a match
 * 1. Levenshtein Edit Distance (LED) – default is 0.8 if LED match is used, 
 * signature for user defined threshold id LED(threshold), i.e.<b>
 * &lt;Rule Ident="FledLDS"&gt;
 *     &lt;Term Item="StudentFirstName" MatchResult="LED(0.8)"/&gt;
 *     &lt;Term Item="StudentLastName" MatchResult="Exact_Ignore_Case"/&gt;
 *     &lt;Term Item="StudentDateOfBirth" MatchResult="Exact"/&gt;
 *     &lt;Term Item="StudentSSN" MatchResult="Exact"/&gt;
 * &lt;/Rule&gt;
 * <b>
 * For more info see http://en.wikipedia.org/wiki/Levenshtein_distance. <b>
 *  
 * 2. These all come under the heading of substring, Substring Left (Prefix) 
 * Substring Right (Suffix), and Substring Middle. I am also thinking about 
 * adding Subsequences, Border and Proper Substring.<b>
 * <ul>
 * <li>· SUBSTRLEFT(length) – a source and target are equivalent if the first x 
 * characters starting from the left are the same, i.e. SubStrLeft(4) makes 
 * MaryAnne ≈ Mary.</li>
 * <li>· SUBSTRRIGHT(length) – a source and target are equivalent if the last x 
 * characters starting from the right are the same, i.e SubStrRight(4) makes 
 * MaryAnne ≈ Anne.</li>
 * <li>· SUBSTRMID(start, length) – a source and target are equivalent if the if
 * the middle characters start from position x for a length of l are the same, 
 * SubStrMid(2,6) makes Krystal ≈ Crystalline.</li>
 * </ul><b>
 * For Example: <b>
 * &lt;Rule Ident="F5L5DS"&gt;
 *     &lt;Term Item="StudentFirstName" MatchResult="SUBSTRLEFT(5)"/&gt;
 *     &lt;Term Item="StudentLastName" MatchResult="SUBSTRMID(2, 5)"/&gt;
 *     &lt;Term Item="StudentDateOfBirth" MatchResult="Exact"/&gt;
 *     &lt;Term Item="StudentSSN" MatchResult="Exact"/&gt;
 * &lt;/Rule&gt;
 * <b>
 * Created on Feb 17, 2012 12:00:25 AM
 * @author enelso
 */
public class OysterComparePhone extends OysterComparator {
    /** Single Character Transpose Utility */
    private OysterUtilityTranspose transpose;
    
    /** Levenshtein Edit Distance */
    private OysterEditDistance editDist;

    /** Sub String Matches */
    private CharacterSubstringMatches substr;
    
    /**
     * Creates a new instance of OysterComparePhone
     */
    public OysterComparePhone(){
        super();
        String [] arr = {"PHONEMATCH","TRANSPOSE","LED","SUBSTRLEFT","SUBSTRRIGHT","SUBSTRMID"};
        for (int i = 0; i < arr.length; i++){
            matchCodes.add(arr[i]);
            matchCodes.add("~"+arr[i]);
        }
        
        transpose = new OysterUtilityTranspose();
	editDist = new OysterEditDistance();
        substr = new CharacterSubstringMatches();
    }
    
    /**
     * 
     * @param s source String
     * @param t target String
     * @param matchType the type of match to preform.
     * @return PhoneMatch, Transpose, LED, SubStrLeft, SubStrRight, SubStrMid or X
     */
    @Override
    public String getMatchCode (String s, String t, String matchType) {
        String result, tempMatchType = matchType;
        String sTemp = replaceAlpha(s);
        String tTemp = replaceAlpha(t);
        int length = 0, start = 0;
        float ledThreshold = 0.8f;
        boolean not = false;
        
        // Check for NOT operator
        if (matchType.toUpperCase(Locale.US).startsWith("~")){
            matchType = matchType.substring(1);
            not = true;
        }
        
        //======================================================================
        //  Get Funtionized arguments from Utilities
        //======================================================================
        if (matchType.toUpperCase(Locale.US).startsWith("SUBSTRLEFT(")){
            matchType = matchType.trim().substring(11, matchType.length()-1);
            
            length = Integer.parseInt(matchType);
            matchType = "SubStrLeft";
        } else if (matchType.toUpperCase(Locale.US).startsWith("SUBSTRRIGHT(")){
            matchType = matchType.trim().substring(12, matchType.length()-1);
            
            length = Integer.parseInt(matchType);
            matchType = "SubStrRight";
        } else if (matchType.toUpperCase(Locale.US).startsWith("SUBSTRMID(")){
            matchType = matchType.trim().substring(10, matchType.length()-1);
            String temp[] = matchType.split("[,]");
            
            start = Integer.parseInt(temp[0]);
            length = Integer.parseInt(temp[1]);
            
            matchType = "SubStrMid";
        } else if (matchType.toUpperCase(Locale.US).startsWith("PSUBSTR(")){
            matchType = matchType.trim().substring(8, matchType.length()-1);
            
            length = Integer.parseInt(matchType);
            matchType = "PSubStr";
        } else if (matchType.toUpperCase(Locale.US).startsWith("LED(")){
            matchType = matchType.trim().substring(4, matchType.length()-1);
            
            ledThreshold = Float.parseFloat(matchType);
            matchType = "LED";
        }
        
        //======================================================================
        //======================================================================
        if (!not) {
        if (matchType.equalsIgnoreCase("PhoneMatch") && sTemp.equals(tTemp)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("Transpose") && transpose.differByTranspose(sTemp, tTemp)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("SubStrLeft") && substr.left(sTemp, tTemp, length)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("SubStrRight") && substr.right(sTemp, tTemp, length)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("SubStrMid") && substr.mid(sTemp, tTemp, start, length)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("LED")){
            // calculate edit distance
            editDist.computeDistance(sTemp, tTemp);
            
            // if greater than or equal to normalized score it's a match
            if (editDist.computeNormalizedScore() >= ledThreshold) {
                result = tempMatchType;
            } else {
                result = "X";
            }
        } else {
            result = "X";
        }
        } else {
            if (matchType.equalsIgnoreCase("PhoneMatch") && !sTemp.equals(tTemp)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("Transpose") && !transpose.differByTranspose(sTemp, tTemp)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrLeft") && !substr.left(sTemp, tTemp, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrRight") && !substr.right(sTemp, tTemp, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrMid") && !substr.mid(sTemp, tTemp, start, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("LED")) {
                // calculate edit distance
                editDist.computeDistance(sTemp, tTemp);

                // if greater than or equal to normalized score it's a match
                if (!(editDist.computeNormalizedScore() >= ledThreshold)) {
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

    /**
     * This method replaced letters in phone numbers with their numeric position
     * on a phone keypad, i.e. 555-TAXI -> 555-8294.
     * @param s
     * @return 
     */
    private String replaceAlpha(String s) {
        String result = "";
        
        if (s != null) {
            result = s.toUpperCase();
            result = result.replaceAll("[ABC]","2");
            result = result.replaceAll("[DEF]","3");
            result = result.replaceAll("[GHI]","4");
            result = result.replaceAll("[JKL]","5");
            result = result.replaceAll("[MNO]","6");
            result = result.replaceAll("[PQRS]","7");
            result = result.replaceAll("[TUV]","8");
            result = result.replaceAll("[WXYZ]","9");
            result = result.replaceAll("\\D", "");
        }
        
        return result;
    }
}
