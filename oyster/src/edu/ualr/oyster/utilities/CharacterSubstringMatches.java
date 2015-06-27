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
 * http://en.wikipedia.org/wiki/Substring
 * @author Eric D. Nelson
 */
public class CharacterSubstringMatches {
    /**
     * Determines if a source and target are equivalent based on if the first x 
     * characters starting from the left are the same, i.e. SubStrLeft(4) makes 
     * MaryAnne ≈ Mary 
     * @param s is source String
     * @param t
     * @param length is the number of characters from the start position that 
     * will be copied.
     * @return true is a match occurs, otherwise false
     */
    public boolean left(String s, String t, int length){
        boolean flag = false;
        if (s == null || s.length() < length) {
            flag = false;
        } else if (t == null || t.length() < length) {
            flag = false;
        } else if (length < 1) {
            flag = false;
        }
        else {
            if(s.substring(0, length).equalsIgnoreCase(t.substring(0, length))){
                flag = true;
            }
        }
        return flag;
    }
    
    /**
     * Determines if a source and target are equivalent based on if the last x 
     * characters starting from the right are the same, i.e SubStrRight(4) makes
     * MaryAnne ≈ Anne.
     * @param s is source String
     * @param t
     * @param length is the number of characters from the start position that 
     * will be copied.
     * @return true is a match occurs, otherwise false
     */
    public boolean right(String s, String t, int length){
        boolean flag = false;
        if (s == null || s.length() < length) {
            flag = false;
        } else if (t == null || t.length() < length) {
            flag = false;
        } else if (length < 1) {
            flag = false;
        }
        else {
            if(s.substring(s.length()-length).equalsIgnoreCase(t.substring(t.length()-length))){
                flag = true;
            }
        }
        return flag;
    }
    
    /**
     * Determines if a source and target are equivalent base on if the middle 
     * characters starting from position x for a length of l are the same, 
     * SubStrMid(2,6) makes Krystal ≈ Crystalline.
     * @param s is source String
     * @param t is KB/Candidate target String
     * @param start is the starting position within the string to begin
     * @param length is the number of characters from the start position that 
     * will be copied.
     * @return true is a match occurs, otherwise false
     */
    public boolean mid(String s, String t, int start, int length){
        boolean flag = false;
        if (s == null || s.length() < start+length) {
            flag = false;
        } else if (t == null || t.length() < start+length) {
            flag = false;
        } else if (length < 1) {
            flag = false;
        } else if (start < 0 ) {
            flag = false;
        }
        else {
            if(s.substring(start, start+length).equalsIgnoreCase(t.substring(start, start+length))){
                flag = true;
            }
        }
        return flag;
    }
    
    /**
     * If A is a substring of, but not equal to, B, then A is called a proper 
     * substring of B, written A ⊊ B (A is a proper substring of B) or B ⊋ A 
     * (B is a proper super-string of A).
     * @param s is source String
     * @param t is KB/Candidate target String
     * @param minSize - the minimum size strings to compare
     * @return true is a match occurs, otherwise false
     */
    public boolean properSubString(String s, String t, int minSize){
        boolean flag = false;
        
        if (s != null && t != null) {
        if (s.length() >= minSize && t.length() >= minSize){
            if (t.toLowerCase(Locale.US).contains(s.toLowerCase(Locale.US))) {
                flag = true;
                } else if (s.toLowerCase(Locale.US).contains(t.toLowerCase(Locale.US))) {
                    flag = true;
                }
            }
        }
        
        return flag;
    }

    public String getLeft(String s, int length){
        String result = null;
        
        if (s != null){
            if (s.length() >= length){
                result = s.substring(0, length);
            }
            else {
                result = s;
            }
        }
        
        return result;
    }
    
    public String getRight(String s, int length){
        String result = null;
        
        if (s != null){
            if (s.length() >= length){
                result = s.substring(s.length()-length);
            }
            else {
                result = s;
            }
        }
        
        return result;
    }
    
    public String getMid(String s, int start, int length){
        String result = null;
        
        if (s != null){
            if (s.length() >= length){
                if (s.length() >= start+length) {
                    result = s.substring(start, start+length);
                }
                else {
                    result = "";
                }
            }
            else {
                result = "";
            }
        }
        
        return result;
    }
}
