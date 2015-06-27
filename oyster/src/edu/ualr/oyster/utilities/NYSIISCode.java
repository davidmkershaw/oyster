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

package edu.ualr.oyster.utilities;

import java.util.Locale;

/**
 * NYSIISCode.java
 * Created on May 15, 2010
 * 
 * The New York State Identification and Intelligence System Phonetic Code, 
 * commonly known as NYSIIS, is a phonetic algorithm devised in 1970 as part of
 * the New York State Identification and Intelligence System (now a part of the 
 * New York State Division of Criminal Justice Services). Algorithm taken from 
 * http://en.wikipedia.org/wiki/New_York_State_Identification_and_Intelligence_System.
 * 
 * More information can be found at "Name Search Techniques" by R. L. Taft. 
 * 
 * @author Eric D. Nelson
 */
public class NYSIISCode {
    /**
     * Creates a new instance of NYSIISCode
     */
    public NYSIISCode(){
    }
    
    /**
     * This method determines the New York State Identification and Intelligence  
     * System Phonetic code for the input String. 
     * @param s The input string
     * @return a String containing the NYSIIS encoding
     */
    public String getNYSIISCode(String s){
        String result = null;
        
        if (s != null && !s.trim().equals("")){
            String temp = s.toUpperCase(Locale.US).trim();
            
            // Standardize the string by removing all punctuations and spaces
            temp = temp.replaceAll("[^\\w]", "");
            temp = temp.replaceAll("[\\d]", "");
            
            // Step 1. Replace the first letters of the name
            if (temp.startsWith("MAC")){
                temp = "MCC" + temp.substring(3);
            } else if (temp.startsWith("KN")){
                temp = "NN" + temp.substring(2);
            } else if (temp.startsWith("K")){
                temp = "C" + temp.substring(1);
            } else if (temp.startsWith("PH")){
                temp = "FF" + temp.substring(2);
            } else if (temp.startsWith("PF")){
                temp = "FF" + temp.substring(2);
            } else if (temp.startsWith("SCH")){
                temp = "SSS" + temp.substring(3);
            }
            
            // Step 2. Replace the last letters of the name
            if (temp.endsWith("EE")){
                temp = temp.substring(0, temp.length()-2) + "Y ";
            } else if (temp.endsWith("IE")){
                temp = temp.substring(0, temp.length()-2) + "Y ";
            } else if (temp.endsWith("DT") || temp.endsWith("RT") || temp.endsWith("RD") ||
                     temp.endsWith("NT") || temp.endsWith("ND")){
                temp = temp.substring(0, temp.length()-2) + "D ";
            }
            
            // 3. Get the first letter
            result = "" + s.charAt(0);
            
            // 4. Encode the String
            char c;
            for (int i = 1; i < temp.length(); i++){
                c = temp.charAt(i);
                
                if (isVowel(c)){
                    if (c == 'E' && (i+1 < temp.length() && temp.charAt(i+1) == 'V')) {
                        result += "AF";
                    } else {
                        result += "A";
                    }
                } else if (c == 'Q') {
                    result += "G";
                } else if (c == 'Z') {
                    result += "S";
                } else if (c == 'M') {
                        result += "N";
                } else if (c == 'K'){
                    if (i+1 < temp.length() && temp.charAt(i+1) == 'N') {
                        result += "N";
                    } else {
                        result += "C";
                    }
                } else if ((i+3 < temp.length()) && temp.substring(i, i+3).equals("SCH")){
                    result += "SSS";
                } else if ((i+2 < temp.length()) && temp.substring(i, i+2).equals("PH")){
                    result += "FF";
                } else if (c == 'H' && (i > 0 && !isVowel(temp.charAt(i-1)) || 
                    (i+1 < temp.length() && !isVowel(temp.charAt(i+1))))){
                    result += temp.charAt(i-1);
                } else if (c == 'W' && (i > 0 && isVowel(temp.charAt(i-1)))){
                    result += temp.charAt(i-1);
                } else {
                    result += c;
                }
            }
            
            if (result.endsWith("S")) {
                result = result.substring(0, result.length()-1);
            }
            if (result.endsWith("AY")) {
                result = result.substring(0, result.length()-2) + "Y";
            }
            if (result.endsWith("A")) {
                result = result.substring(0, result.length()-1);
            }
            
            // 5. Remove duplicate letters
            if (result.length() > 1) {
                c = result.charAt(0);
                for (int i = 1; i < result.length(); i++) {
                    if (c == result.charAt(i)) {
                        result = result.substring(0, i) + result.substring(i + 1);
                        i--;
                    } else if (result.length() > i) {
                        c = result.charAt(i);
                    }
                }
            }
            result = result.trim();
        }
        
        return result;
    }
    
    /**
     * This method compares two String using the NYSIIS Encoding. If the 
     * Strings produce the same encoding then the Strings are considered a 
     * match and true is returned.
     * @param s input source String
     * @param t input target String
     * @return true if the source and target are considered a match, otherwise
     * false.
     */
    public boolean compareNYSIISCodes(String s, String t){
        boolean match = false;
        String sNYSIISCode = getNYSIISCode(s);
        String tNYSIISCode = getNYSIISCode(t);
        
        if (sNYSIISCode !=  null && tNYSIISCode != null) {
            match = sNYSIISCode.equals(tNYSIISCode);
        }
        
        return match;
    }
    
    /**
     * Determines if the input character is a vowel.
     * @param c the character to check
     * @return <code>true</code> if this is vowel; <code>false</code> otherwise.
     */
    private boolean isVowel(char c){
        boolean flag;
        switch (c){
            case 'A':
            case 'E':
            case 'I':
            case 'O':
            case 'U': flag = true; break;
            default: flag = false;
        }
        return flag;
    }
}
