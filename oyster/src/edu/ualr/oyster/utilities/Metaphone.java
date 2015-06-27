/*
 * Copyright 2013 John Talburt, Eric Nelson
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Metaphone is a phonetic algorithm, an algorithm published in 1990 for 
 * indexing words by their English pronunciation. The algorithm should be 
 * limited to English only.
 * 
 * Created on Apr 29, 2012 8:38:38 AM
 * @author Eric D. Nelson
 */
public class Metaphone {
    /**
     * Creates a new instance of Metaphone
     */
    public Metaphone(){
    }

    public String getMetaphone(String s) {
        String result = null, temp = "";

        try {
            if (s != null && s.trim().length() > 0) {
                temp = s.toUpperCase(Locale.US);

                // 1. Standardize the string by removing all punctuations and spaces
                temp = temp.replaceAll("[^\\w]", "");
                temp = temp.replaceAll("[\\d]", "");

                if (temp.trim().length() > 0) {
                    // 2. Drop duplicate adjacent letters, except for C. 
                    temp = dropAdjacentDup(temp);
                    
                    // 3. If the word begins with 'KN', 'GN', 'PN', 'AE', 'WR', drop the first letter.
                    if (temp.startsWith("KN") || temp.startsWith("GN") || temp.startsWith("PN") ||
                        temp.startsWith("AE") || temp.startsWith("WR")) {
                        temp = temp.substring(1);
                    }

                    // 4. Drop 'B' if after 'M' at the end of the word. 
                    if (temp.endsWith("BM")) {
                        temp = temp.substring(0, temp.length()-2) + "M";
                    }
                    // 5. 'C' transforms to 'X' if followed by 'IA' or 'H' 
                    //    (unless in latter case, it is part of '-SCH-', in 
                    //    which case it transforms to 'K'). 'C' transforms to 
                    //    'S' if followed by 'I', 'E', or 'Y'. Otherwise, 'C' 
                    //    transforms to 'K'. 
                    int begin;
                    if ((begin = temp.indexOf("CIA")) != -1){
                        temp = temp.substring(0, begin) + "X" + temp.substring(begin+1);
                    } else if ((begin = temp.indexOf("CH")) != -1 && temp.indexOf("SCH") == -1){
                        temp = temp.substring(0, begin) + "K" + temp.substring(begin+1);
                    } else if ((begin = temp.indexOf("CI")) != -1 || (begin = temp.indexOf("CE")) != -1 ||
                               (begin = temp.indexOf("CY")) != -1){
                        temp = temp.substring(0, begin) + "S" + temp.substring(begin+1);
                    } else {
                        temp = temp.replaceAll("C", "K");
                    }
                    // 6. 'D' transforms to 'J' if followed by 'GE', 'GY', or 'GI'.
                    //    Otherwise, 'D' transforms to 'T'. 
                    if ((begin = temp.indexOf("DGE")) != -1 || (begin = temp.indexOf("DGI")) != -1 ||
                        (begin = temp.indexOf("DGY")) != -1){
                        temp = temp.substring(0, begin) + "J" + temp.substring(begin+1);
                    } else {
                        temp = temp.replaceAll("D", "T");
                    }
                    // 7. Drop 'G' if followed by 'H' and 'H' is not at the end 
                    //    or before a vowel. Drop 'G' if followed by 'N' or 'NED' 
                    //    and is at the end. 
                    if ((begin = temp.indexOf("GH")) != -1 && begin+1 != temp.length() &&
                         (temp.indexOf("GHA") == -1 && temp.indexOf("GHE") == -1 &&
                          temp.indexOf("GHI") == -1 && temp.indexOf("GHO") == -1 &&
                          temp.indexOf("GHU") == -1)){
                        temp = temp.substring(0, begin) + temp.substring(begin+1);
                    } else if (temp.endsWith("GN")){
                        temp = temp.substring(0, temp.length()-2) + "N";
                    } else if (temp.endsWith("GNED")){
                        temp = temp.substring(0, temp.length()-4) + "NED";
                    }
                    // 8. 'G' transforms to 'J' if before 'I', 'E', or 'Y', and
                    //    it is not in 'GG'. Otherwise, 'G' transforms to 'K'. 
                    temp = replace(temp, "G[EIY]", "J", 0);
                    temp = temp.replaceAll("G", "K");
                    // 9. Drop 'H' if after vowel and not before a vowel. 
                    temp = replace(temp, "[^AEIOU]H[AEIOU]", "", 1);
                    // 10. 'CK' transforms to 'K'.
                    temp = temp.replaceAll("CK", "K");
                    // 11. 'PH' transforms to 'F'. 
                    temp = temp.replaceAll("PH", "F");
                    // 12. 'Q' transforms to 'K'. 
                    temp = temp.replaceAll("Q", "K");
                    // 13. 'S' transforms to 'X' if followed by 'H', 'IO', or 'IA'. 
                    temp = replace(temp, "S(H|IO|IA)", "X", 0);
                    // 14. 'T' transforms to 'X' if followed by 'IA' or 'IO'. 
                    //     'TH' transforms to '0'. Drop 'T' if followed by 'CH'. 
                    temp = replace(temp, "TI[AO]", "X", 0);
                    temp = temp.replaceAll("TH", "0");
                    temp = replace(temp, "TCH", "", 0);
                    // 15. 'V' transforms to 'F'. 
                    temp = temp.replaceAll("V", "F");
                    // 16. 'WH' transforms to 'W' if at the beginning. 
                    //     Drop 'W' if not followed by a vowel. 
                    temp = replace(temp, "^WH", "", 1);
                    temp = replace(temp, "W[^AEIOU]", "", 0);
                    // 17. 'X' transforms to 'S' if at the beginning. 
                    //     Otherwise, 'X' transforms to 'KS'. 
                    temp = replace(temp, "^X", "S", 0);
                    temp = temp.replaceAll("X", "KS");
                    // 18. Drop 'Y' if not followed by a vowel. 
                    temp = replace(temp, "Y[^AEIOU]", "", 0);
                    // 19. 'Z' transforms to 'S'. 
                    temp = temp.replaceAll("Z", "S");
                    // 20. Drop all vowels unless it is the beginning. 
                    temp = temp.substring(0, 1) + temp.substring(1).replaceAll("[AEIOU]", "");
                }
                result = temp;
            }
        } catch (RuntimeException ex) {
            Logger.getLogger(Metaphone.class.getName()).log(Level.SEVERE, "s:" + s + ", temp:" + temp + ", result:" + result, ex);
            result = null;
        }
        return result;
    }
    
    /**
     * This method compares two String using the Metaphone. If the 
     * Strings produce the same encoding then the Strings are considered a 
     * match and true is returned.
     * @param s input source String
     * @param t input target String
     * @return true if the source and target are considered a match, otherwise
     * false.
     */
    public boolean compareMetaphone(String s, String t){
        String sMetaphone = getMetaphone(s);
        String tMetaphone = getMetaphone(t);
        
        boolean flag = false;
        if (sMetaphone != null && tMetaphone != null) {
            flag = sMetaphone.equals(tMetaphone);
        }
        
        return flag;
    }

    private String replace(String s, String regex, String replace, int pos) {
        String result;
        Pattern p = Pattern.compile(regex);
        Matcher m = p.matcher(s);
        if (m.find()) {
            result = s.substring(0, m.start()+pos) + replace + s.substring(m.start()+1+pos);
        } else {
            result = s;
        }
        return result;
    }

    private String dropAdjacentDup(String temp) {
        StringBuilder result = new StringBuilder(100);
        
        char c = temp.charAt(0);
        result.append(c);
        for (int i = 1; i < temp.length(); i++){
            if (c != temp.charAt(i)){
                result.append(temp.charAt(i));
            }
            c = temp.charAt(i);
        }
        
        return result.toString();
    }
    
    /**
     * @param args the command line arguments
     */

    public static void main(String[] args) {
        Metaphone m = new Metaphone();
        System.out.format("%1$s   %2$s%n", m.getMetaphone("Steffen"), "STFN");
        System.out.format("%1$s   %2$s%n", m.getMetaphone("Stephen"), "STPN");
        System.out.format("%1$s   %2$s%n", m.getMetaphone("FALLIS"), "FLS");
        System.out.format("%1$s   %2$s%n", m.getMetaphone("VALLIS"), "FLS");
        System.out.format("%1$s   %2$s%n", m.getMetaphone("KLINE"), "KLN");
        System.out.format("%1$s   %2$s%n", m.getMetaphone("CLINE"), "KLN");
    }

}
