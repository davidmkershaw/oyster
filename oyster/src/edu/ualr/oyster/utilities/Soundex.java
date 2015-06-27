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
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * 1. Get the first letter
 * 2. Remove Vowels, W & Y
 * 3. Encode the remaining characters
 *    b, f, p, v → 1 
 *    c, g, j, k, q, s, x, z → 2 
 *    d, t → 3 
 *    l → 4 
 *    m, n → 5 
 *    r → 6 
 * 4. Remove duplicate letters
 * 5. Create 4 digit code
 * 
 * @see <a href="http://en.wikipedia.org/wiki/Soundex"> Soundex </a>
 * @see <a href="http://www.archives.gov/genealogy/census/soundex.html"> The Soundex Indexing System </a>
 * @see <a href="http://www.archives.gov/publications/general-info-leaflets/55.html"> The Soundex Indexing System </a> 
 * @author Eric D. Nelson
 */
public class Soundex {
    /**
     * Creates a new instance of <code>Soundex</code>
     */
    public Soundex(){
    }
    
    /**
     * This method determines the Robert C. Russell and Margaret K. Odell  
     * (American) Soundex hash for the input String. 
     * @param s The input string
     * @return a String containing the Soundex encoding
     */
    public String getSoundex(String s) {
        String result = null, temp = "", firstLetter;
        char c;

        try {
            if (s != null && s.trim().length() > 0) {
                temp = s.toUpperCase(Locale.US);

                // 1. Standardize the string by removing all punctuations and spaces
                temp = temp.replaceAll("\\p{Punct}", "");
                temp = temp.replaceAll("\\p{Space}", "");

                if (temp.trim().length() > 0) {
                    // 2. Get the first letter
                    firstLetter = "" + temp.charAt(0);

                    // 3. Remove Vowels, W & Y
                    temp = temp.replaceAll("[AEHIOUWY]", "0");

                    // 4. Encode the remaining characters
                    result = "";
                    for (int i = 0; i < temp.length(); i++) {
                        c = temp.charAt(i);
                        switch (c) {
                            case 'B':
                            case 'F':
                            case 'P':
                            case 'V':
                                result += '1';
                                break;
                            case 'C':
                            case 'G':
                            case 'J':
                            case 'K':
                            case 'Q':
                            case 'S':
                            case 'X':
                            case 'Z':
                                result += '2';
                                break;
                            case 'D':
                            case 'T':
                                result += '3';
                                break;
                            case 'L':
                                result += '4';
                                break;
                            case 'M':
                            case 'N':
                                result += '5';
                                break;
                            case 'R':
                                result += '6';
                                break;
                            default:
                                result += c;
                        }
                    }

                    // 5. Remove duplicate letters
                    if (result.length() > 0) {
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

                    // 6. Replace the first letter
                    result = firstLetter + result.substring(1);

                    // 7. Replace all zeroes
                    result = result.replaceAll("0", "");

                    // 8. Create 4 digit code
                    if (result.length() > 4) {
                        result = result.substring(0, 4);
                    } else if (result.length() < 4) {
                        for (int i = result.length(); i < 4; i++) {
                            result += "0";
                        }
                    }
                }
            }
        } catch (RuntimeException ex) {
            Logger.getLogger(Soundex.class.getName()).log(Level.SEVERE, "s:" + s + ", temp:" + temp + ", result:" + result, ex);
            result = null;
        }
        return result;
    }
    
    /**
     * This method compares two String using the American Soundex. If the 
     * Strings produce the same encoding then the Strings are considered a 
     * match and true is returned.
     * @param s input source String
     * @param t input target String
     * @return true if the source and target are considered a match, otherwise
     * false.
     */
    public boolean compareSoundex(String s, String t){
        String sSoundex = getSoundex(s);
        String tSoundex = getSoundex(t);
        
        boolean flag = false;
        if (sSoundex != null && tSoundex != null) {
            flag = sSoundex.equals(tSoundex);
        }
        
        return flag;
    }
    
    /*
    public static void main (String[] args) {
        Soundex s = new Soundex();
        System.out.println(s.getSoundex("Harper"));
    }
    */
}
