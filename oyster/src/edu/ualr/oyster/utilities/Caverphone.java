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
 * The Caverphone phonetic matching algorithm was created by David Hood in the 
 * Caversham Project at the University of Otago in New Zealand in 2002, revised 
 * in 2004. It was created to assist in data matching between late 19th century 
 * and early 20th century electoral rolls, where the name only needed to be in a
 * "commonly recognizable form". The algorithm was intended to apply to those 
 * names that could not easily be matched between electoral rolls, after the 
 * exact matches were removed from the pool of potential matches). The algorithm
 * is optimized for accents present in the study area (southern part of the city
 * of Dunedin, New Zealand).
 * 
 * (Excerpt taken from Wikipedia)
 * Created on Apr 29, 2012 9:43:39 AM
 * @see http://caversham.otago.ac.nz/files/working/ctp060902.pdf 
 * @author Eric D. Nelson
 */
public class Caverphone {
    /**
     * Creates a new instance of Caverphone
     */
    public Caverphone(){
    }

    /**
     * This method determines the David Hood Caverphone hash for the input string. 
     * @param s The input string
     * @return a String containing the Caverphone encoding
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
                
                // III. If the name starts with 
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
                result = result.replaceAll("gn", "2n");
                
                //  IV. If the name ends with 
                //        1. mb make it m2 
                if (result.endsWith("mb")) {
                    result = result.substring(0, result.length()-2) + "m2";
                }
                
                //   V. Replace 
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
                //       20. 3gh3 with 3kh3 
                result = result.replaceAll("3gh3", "3kh3");
                //       21. gh with 22 
                result = result.replaceAll("gh", "22");
                //       22. g with k 
                result = result.replaceAll("g", "k");
                //       23. groups of the letter s with a S 
                result = result.replaceAll("s+", "S");
                //       24. groups of the letter t with a T 
                result = result.replaceAll("t+", "T");
                //       25. groups of the letter p with a P 
                result = result.replaceAll("p+", "P");
                //       26. groups of the letter k with a K 
                result = result.replaceAll("k+", "K");
                //       27. groups of the letter f with a F 
                result = result.replaceAll("f+", "F");
                //       28. groups of the letter m with a M 
                result = result.replaceAll("m+", "M");
                //       29. groups of the letter n with a N 
                result = result.replaceAll("n+", "N");
                //       30. w3 with W3 
                result = result.replaceAll("w3", "W3");
                //       31. wy with Wy 
                result = result.replaceAll("wy", "Wy");
                //       32. wh3 with Wh3 
                result = result.replaceAll("wh3", "Wh3");
                //       33. why with Why 
                result = result.replaceAll("why", "Why");
                //       34. w with 2 
                result = result.replaceAll("w", "2");
                //       35. any initial h with an A 
                if (result.startsWith("h")) {
                    result = result.replaceFirst("h", "A");
                }
                //       36. all other occurrences of h with a 2 
                result = result.replaceAll("h", "2");
                //       37. r3 with R3 
                result = result.replaceAll("r3", "R3");
                //       38. ry with Ry 
                result = result.replaceAll("ry", "Ry");
                //       39. r with 2 
                result = result.replaceAll("r", "2");
                //       40. l3 with L3 
                result = result.replaceAll("l3", "L3");
                //       41. ly with Ly 
                result = result.replaceAll("ly", "Ly");
                //       42. l with 2 
                result = result.replaceAll("l", "2");
                //       43. j with y 
                result = result.replaceAll("j", "y");
                //       44. y3 with Y3 
                result = result.replaceAll("y3", "Y3");
                //       45. y with 2 
                result = result.replaceAll("y", "2");
                
                //   VI. remove all 
                //        1. 2's 
                result = result.replaceAll("2", "");
                //        2. 3's 
                result = result.replaceAll("3", "");
                
                //  VII. put six 1s on the end
                result += "111111";
                
                // VIII. take the first six characters as the code 
                if (result.length() > 6) {
                    result = result.substring(0, 6);
                }
            }
        } catch (RuntimeException ex) {
            Logger.getLogger(Caverphone.class.getName()).log(Level.SEVERE, "s:" + s + ", result:" + result, ex);
            result = null;
        }
        return result;
    }
    
    /**
     * This method compares two String using the Caverphone encoding. If the 
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
        Caverphone c = new Caverphone();
        System.out.format("%1$s   %2$s%n", c.getCaverphone("Lee"), "L11111");
        System.out.format("%1$s   %2$s%n", c.getCaverphone("Thompson"), "TMPSN1");
    }
*/
}
