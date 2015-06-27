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

/**
 * The Caverphone2 phonetic matching algorithm was created by David Hood in the 
 * Caversham Project at the University of Otago in New Zealand in 2004.
 * 
 * Created on Apr 29, 2012 9:43:39 AM
 * @see http://caversham.otago.ac.nz/files/working/ctp150804.pdf
 * @author Eric D. Nelson
 */
public class Caverphone2 {
    /**
     * Creates a new instance of Caverphone2
     */
    public Caverphone2(){
    }

    /**
     * This method determines the David Hood Caverphone 2.0 hash for the input 
     * string. 
     * @param s The input string
     * @return a String containing the Caverphone 2.0 encoding
     */
    public String getCaverphone(String s) {
        String result = null;

        try {
            if (s != null){
                //   I. Convert to lowercase 
                result = s.toLowerCase(Locale.US);
                
                //  II. Remove anything not A-Z 
                result = result.replaceAll("[^\\w]", "");
                result = result.replaceAll("[\\d]", "");
                
                // III. Remove final e
                if (result.endsWith("e")) {
                    result = result.substring(0, result.length()-1);
                }
                
                // IV. If the name starts with 
                //        1. cough make it cou2f 
                if (result.startsWith("cough")) {
                    result = "cou2f" + result.substring(5);
                }
                //        2. rough make it rou2f 
                if (result.startsWith("rough")) {
                    result = "rou2f" + result.substring(5);
                }
                //        3. tough make it tou2f 
                if (result.startsWith("tough")) {
                    result = "tou2f" + result.substring(5);
                }
                //        4. enough make it enou2f 
                if (result.startsWith("enough")) {
                    result = "enou2f" + result.substring(6);
                }
                //        5. gn make it 2n 
                result = result.replaceAll("^gn", "2n");
                
                // V. If the name ends with 
                //        1. mb make it m2 
                if (result.endsWith("mb")) {
                    result = result.substring(0, result.length()-2) + "m2";
                }
                
                // VI. Replace 
                //        1. cq with 2q 
                result = result.replaceAll("cq", "2q");
                //        2. ci with si 
                result = result.replaceAll("ci", "si");
                //        3. ce with se 
                result = result.replaceAll("ce", "se");
                //        4. cy with sy 
                result = result.replaceAll("cy", "sy");
                //        5. tch with 2ch 
                result = result.replaceAll("tch", "2ch");
                //        6. c with k 
                result = result.replaceAll("c", "k");
                //        7. q with k 
                result = result.replaceAll("q", "k");
                //        8. x with k 
                result = result.replaceAll("x", "k");
                //        9. v with f 
                result = result.replaceAll("v", "f");
                //       10. dg with 2g 
                result = result.replaceAll("dg", "2g");
                //       11. tio with sio 
                result = result.replaceAll("tio", "sio");
                //       12. tia with sia 
                result = result.replaceAll("tia", "sia");
                //       13. d with t 
                result = result.replaceAll("d", "t");
                //       14. ph with fh 
                result = result.replaceAll("ph", "fh");
                //       15. b with p 
                result = result.replaceAll("b", "p");
                //       16. sh with s2 
                result = result.replaceAll("sh", "s2");
                //       17. z with s 
                result = result.replaceAll("z", "s");
                //       18. any initial vowel with an A 
                // FIXME: Vowels are normally a,e,i,o,u but depending on the data might include characters such as æ, ā, or ø
                if (result.startsWith("a") || result.startsWith("e") || result.startsWith("i") ||
                    result.startsWith("o") || result.startsWith("u")) {
                    result = result.replaceFirst("[aeiou]", "A");
                }
                //       19. all other vowels with a 3 
                result = result.replaceAll("[aeiou]", "3");
                //       20. replace j with y
                result = result.replaceAll("j", "y");
                //       21. replace an initial y3 with Y3
                result = result.replaceAll("^y3", "Y3");
                //       22. replace an initial y with A
                if (result.startsWith("y")) {
                    result = result.replaceFirst("y", "A");
                }
                //       23. replace y with 3
                result = result.replaceAll("y", "3");
                //       24. 3gh3 with 3kh3 
                result = result.replaceAll("3gh3", "3kh3");
                //       25. gh with 22 
                result = result.replaceAll("gh", "22");
                //       26. g with k 
                result = result.replaceAll("g", "k");
                //       27. groups of the letter s with a S 
                result = result.replaceAll("s+", "S");
                //       28. groups of the letter t with a T 
                result = result.replaceAll("t+", "T");
                //       29. groups of the letter p with a P 
                result = result.replaceAll("p+", "P");
                //       30. groups of the letter k with a K 
                result = result.replaceAll("k+", "K");
                //       31. groups of the letter f with a F 
                result = result.replaceAll("f+", "F");
                //       32. groups of the letter m with a M 
                result = result.replaceAll("m+", "M");
                //       33. groups of the letter n with a N 
                result = result.replaceAll("n+", "N");
                //       34. w3 with W3 
                result = result.replaceAll("w3", "W3");
                result = result.replaceAll("wh3", "Wh3");
                //       35. if the name ends in w replace the final w with 3
                if (result.endsWith("w")) {
                    result = result.substring(0, result.length()-1) + "3";
                }
                //       36. replace w with 2
                result = result.replaceAll("w", "2");
                //       37. replace an initial h with an A
                if (result.startsWith("h")) {
                    result = result.replaceFirst("h", "A");
                }
                //       38. replace all other occurrences of h with a 2
                result = result.replaceAll("h", "2");
                //       39. replace r3 with R3
                result = result.replaceAll("r3", "R3");
                //       40. if the name ends in r replace the replace final r with 3
                if (result.endsWith("r")) {
                    result = result.substring(0, result.length()-1) + "3";
                }
                //       41. replace r with 2
                result = result.replaceAll("r", "2");
                //       42. replace l3 with L3
                result = result.replaceAll("l3", "L3");
                //       43. if the name ends in l replace the replace final l with 3
                if (result.endsWith("l")) {
                    result = result.substring(0, result.length()-1) + "3";
                }
                //       44. replace l with 2
                result = result.replaceAll("l", "2");
                //       45. if the name end in 3, replace the final 3 with A
                if (result.endsWith("3")) {
                    result = result.substring(0, result.length()-1) + "A";
                }
                
                // VII. remove all 
                //        1. 2's 
                result = result.replaceAll("2", "");
                //        2. 3's 
                result = result.replaceAll("3", "");
                
                // VIII. put ten 1s on the end
                result += "1111111111";
                
                // IX. take the first ten characters as the code 
                if (result.length() > 10) {
                    result = result.substring(0, 10);
                }
            }
        } catch (RuntimeException ex) {
            Logger.getLogger(Caverphone2.class.getName()).log(Level.SEVERE, "s:" + s + ", result:" + result, ex);
            result = null;
        }
        return result;
    }
    
    /**
     * This method compares two String using the Caverphone 2.0 encoding. If the 
     * Strings produce the same encoding then the Strings are considered a 
     * match and true is returned.
     * @param s input source String
     * @param t input target String
     * @return true if the source and target are considered a match, otherwise
     * false.
     */
    public boolean compareCaverphone(String s, String t){
        String sCaverphone = getCaverphone(s);
        String tCaverphone = getCaverphone(t);
        
        boolean flag = false;
        if (sCaverphone != null && tCaverphone != null) {
            flag = sCaverphone.equals(tCaverphone);
        }
        
        return flag;
    }

    /**
     * @param args the command line arguments
     */
/*
    public static void main(String[] args) {
        Caverphone2 c = new Caverphone2();
        System.out.format("%1$s   %2$s%n", c.getCaverphone("Lee"), "L11111");
        System.out.format("%1$s   %2$s%n", c.getCaverphone("Thompson"), "TMPSN1");
        
        System.out.format("%1$s   %2$s%n", c.getCaverphone("David"), "David");
        System.out.format("%1$s   %2$s%n", c.getCaverphone("Whittle"), "Whittle");
    }
*/
}
