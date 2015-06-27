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

import edu.ualr.oyster.ErrorFormatter;
import edu.ualr.oyster.utilities.CharacterSubstringMatches;
import edu.ualr.oyster.utilities.OysterUtilityTranspose;
import java.util.Locale;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * SSN Comparator class.
 *
 * @author Eric D. Nelson
 */
public class OysterCompareSSN extends OysterComparator {
    /** Single character transposition operator */
    private OysterUtilityTranspose transpose;
    
    /** Substring operator */
    private CharacterSubstringMatches substr;
    
    /**
     * Creates a new instance of <code>OysterCompareSSN</code>.
     */
    public OysterCompareSSN(){
        super();
        
        String [] arr = {"TRANSPOSE","LEADINGZERO","SUBSTRLEFT","SUBSTRRIGHT","SUBSTRMID","PSUBSTR"};
        for (int i = 0; i < arr.length; i++){
            matchCodes.add(arr[i]);
            matchCodes.add("~"+arr[i]);
        }
        
        transpose = new OysterUtilityTranspose();
        substr = new CharacterSubstringMatches();
    }
    
    /**
     * Returns the match code for this <code>OysterCompareADEFirstName</code>.
     * @param s source String.
     * @param t target String.
     * @param matchType the type of match to preform.
     * @return the match code.
     */
    @Override
    public String getMatchCode (String s, String t, String matchType) {
        String result, tempMatchType = matchType;
        int length = 0, start = 0;
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
        }
        
        //======================================================================
        //======================================================================
//        if (isValidSSN(s) && isValidSSN(t)){
        if (!not) {
            if (matchType.equalsIgnoreCase("Transpose") && transpose.differByTranspose(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("LeadingZero")) {
                if (s != null && s.length() > 8 && t != null && t.length() > 8){
                    if (s.substring(0, 1).equals("0") && t.substring(0, 8).equals(s.substring(1, 9))) {
                        result = tempMatchType;
                    } else if (t.substring(0, 1).equals("0") && s.substring(0, 8).equals(t.substring(1, 9))) {
                        result = tempMatchType;
                    } else {
                        result = "X";
                    }
                } else {
                    result = "X";
                }
            } else if (matchType.equalsIgnoreCase("SubStrLeft") && substr.left(s, t, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrRight") && substr.right(s, t, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrMid") && substr.mid(s, t, start, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("PSubStr") && substr.properSubString(s, t, length)) {
                result = tempMatchType;
            } else {
                result = "X";
            }
        } else {
            if (matchType.equalsIgnoreCase("Transpose") && !transpose.differByTranspose(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("LeadingZero")) {
                if (s != null && s.length() > 8 && t != null && t.length() > 8){
                    if (!(s.substring(0, 1).equals("0") && t.substring(0, 8).equals(s.substring(1, 9)))) {
                        result = tempMatchType;
                    } else if (!(t.substring(0, 1).equals("0") && s.substring(0, 8).equals(t.substring(1, 9)))) {
                        result = tempMatchType;
                    } else {
                        result = "X";
                    }
                } else {
                    result = "X";
                }
            } else if (matchType.equalsIgnoreCase("SubStrLeft") && !substr.left(s, t, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrRight") && !substr.right(s, t, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrMid") && !substr.mid(s, t, start, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("PSubStr") && !substr.properSubString(s, t, length)) {
                result = tempMatchType;
            } else {
                result = "X";
            }
        }
  //      }
  //      else result = "X";
        
        return result.toUpperCase();
    }
    
    /**
     * This method determines if an SSN is valid based on the following commonly
     * know rules:
     * <ul>
     * <li>Must be 9 characters.</li>
     * <li>The first character must be less than 8</li>
     * <li>The first three characters must be greater than 000</li>
     * <li>The mid two characters (positions 4 & 5) cannot be equal to 00</li>
     * <li>The last four characters cannot be 0000</li>
     * <li>The SSN must be all numeric characters</li>
     * </ul>
     * @param s the SSN to be validated.
     * @return true if the SSN is valid, otherwise false.
     */
    private boolean isValidSSN(String s) {
        boolean valid = false;
        
        try {
            if (s.length() == 9 && Integer.parseInt(s.substring(0, 1)) < 8 &&
                Integer.parseInt(s.substring(0, 3)) > 0 && !s.substring(3, 5).equals("00") &&
                !s.substring(5).equals("0000")){
                valid = true;
                
                if (commonFakeSSN(s)) {
                    valid = false;
                }
            }
        } catch (RuntimeException ex){
            Logger.getLogger(OysterCompareSSN.class.getName()).log(Level.WARNING, ErrorFormatter.format(ex), ex);
        }
        return valid;
    }
    
    /**
     * This method checks to see that the SSN is not a commonly used fake SSN
     * @param s the SSN to be checked
     * @return true if not a commonly used fake SSN, otherwise false.
     */
    private boolean commonFakeSSN(String s){
        boolean fake = false;
    
        if (s.contains("0000000") || s.contains("1111111") || s.contains("2222222") ||
            s.contains("3333333") || s.contains("4444444") || s.contains("5555555") ||
            s.contains("6666666") || s.contains("7777777") || s.contains("8888888") ||
            s.contains("9999999") || s.contains("1234567") || s.contains("9876543")) {
            fake = true;
        }
        
        return fake;
    }
}
