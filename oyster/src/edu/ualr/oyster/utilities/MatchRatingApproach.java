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
 * MatchRatingApproach.java
 * Created on May 16, 2010
 * 
 * This class is based on the algorithm developed by Western Airlines. More
 * information can be found at:
 * <br>
 * <ul>
 * <li>http://en.wikipedia.org/wiki/Match_Rating_Approach</li>
 * <li>"An Overview of the Issues Related to the use of Personal Identifiers" by 
 * Mark Armstrong</li>
 * </ul>  
 * <br>
 * Encoding Rules
 * 1. Delete all vowels unless the vowel begins the word 
 * 2. Remove the second consonant of any double consonants present 
 * 3. Reduce codex to 6 letters by joining the first 3 and last 3 letters only 
 * <br>
 * Comparison Rules
 * 1. If the length difference between the encoded strings is 3 or greater, then
 *    no similarity comparison is done. 
 * 2. Obtain the minimum rating value by calculating the length sum of the 
 *    encoded strings and using table A 
 * 3. Process the encoded strings from left to right and remove any identical 
 *    characters found from both strings respectively. 
 * 4. Process the unmatched characters from right to left and remove any 
 *    identical characters found from both names respectively. 
 * 5. Subtract the number of unmatched characters from 6 in the longer string. 
 *    This is the similarity rating. 
 * 6. If the similarity rating equal to or greater than the minimum rating then 
 *    the match is considered good.
 * 
 * @author Eric D. Nelson
 */
public class MatchRatingApproach {
    /**
     * Creates a new instance of MatchRatingApproach
     */
    public MatchRatingApproach(){
    }
    
    /**
     * This method determines the Western Airlines encoding for the input String. 
     * @param s The input string
     * @return a String containing the encoding
     */
    public String getMatchRatingApproachCode(String s){
        String result = null;
        char c;
        
        if (s != null && s.length() > 0){
            result = s.toUpperCase(Locale.US);
            
            // Standardize the string by removing all punctuations and digits
            result = result.replaceAll("\\p{Punct}", "");
            result = result.replaceAll("[\\d]", "");
            
            // 1. Deletion of all vowels unless the vowel is the first character
            // of the surname.
            if (isVowel(result.charAt(0))){
                result = result.charAt(0) + result.replaceAll("[AEIOU]", "").trim();
            } else {
                result = result.replaceAll("[AEIOU]", "").trim();
            }
            
            // 2. Elimination of all double consonants by deleting the second 
            // contiguous usage of any consonant.
            c = result.charAt(0);
            for (int i = 1; i < result.length(); i++){
                if (c == result.charAt(i)){
                    result = result.substring(0, i) + result.substring(i+1);
                    i--;
                } else if (result.length() > i){
                    c = result.charAt(i);
                }
            }
            
            // 3. Reduce all encoded names to a maximum of six characters. 
            // This is done by retaining the first three and the last three
            // encoded characters.
            if (result.length() > 6){
                result = result.substring(0, 3) + result.substring(result.length()-3);
            }
        }
        
        return result;
    }
    
    /** Obtain the minimum rating value by calculating the length sum of
     *  the encoded strings
     * @param s the source string
     * @param t the target string
     * @return the minimum rating value
     */
    public int minimumRating(String s, String t){
        int minRating = 0;
        if (s == null && t != null){
            minRating = t.length();
        } else if (s != null && t == null){
            minRating = s.length();
        } else if (s != null && t != null){
            minRating = s.length() + t.length();
            if (minRating <= 4) {
                minRating = 5;
            } else if (4 < minRating && minRating <= 7) {
                minRating = 4;
            } else if (7 < minRating && minRating <= 11) {
                minRating = 3;
            } else if (minRating == 12) {
                minRating = 2;
            } 
        }
        return minRating;
    }
    
    /** Process the encoded strings from left to right and remove any identical 
     *  characters found from both strings respectively. Process the unmatched 
     *  characters from right to left and remove any identical characters found 
     *  from both names respectively. Subtract the number of unmatched characters
     *  from 6 in the longer string. This is the similarity rating.
     * @param s the source string
     * @param t the target string
     * @return the similarity rating
     */
    public int similarityRating(String s, String t){
        int result = 0;
        if (s != null && t != null){
            for (int i = 0; i < Math.min(s.length(), t.length()); i++){
                if (s.charAt(i) == t.charAt(i)){
                    s = s.substring(0, i) + s.substring(i+1);
                    t = t.substring(0, i) + t.substring(i+1);
                    i--;
                }
            }
            
            s = reverse(s);
            t = reverse(t);
            for (int i = 0; i < Math.min(s.length(), t.length()); i++){
                if (s.charAt(i) == t.charAt(i)){
                    s = s.substring(0, i) + s.substring(i+1);
                    t = t.substring(0, i) + t.substring(i+1);
                    i--;
                }
            }
            
            result = 6 - Math.max(s.length(), t.length());
        }
        return result;
    }
    
    /**
     * This method compares two String using the Western Airlines Match Rating
     * encoding. If the Strings produce the same encoding then the Strings are
     * considered a match and true is returned.
     * @param s input source String
     * @param t input target String
     * @return true if the source and target are considered a match, otherwise
     * false.
     */
    public boolean compareMatchRatingCodes(String s, String t){
        boolean match = false;
        
        String sCode =  getMatchRatingApproachCode(s);
        String tCode = getMatchRatingApproachCode(t);
        
        if (sCode != null && tCode != null &&
                Math.abs(sCode.length() - tCode.length()) < 3){
            int mRating = minimumRating(sCode, tCode);
            int sRating = similarityRating(sCode, tCode);
            
            if (sRating >= mRating) {
                match = true;
            }
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
    
    /**
     * Reverses the input string
     * @param s input string
     * @return the reversed string
     */
    private String reverse(String s){
        StringBuffer buf = new StringBuffer();
        buf.append(s);
        buf = buf.reverse();
        return buf.toString();
    }
}
