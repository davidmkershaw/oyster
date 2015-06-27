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
 * This class uses the Levenshtein Edit Distance as the ASM for this utility.
 * The Levenshtein distance between two strings is defined as the minimum number
 * of edits needed to transform one string into the other, with the allowable 
 * edit operations being insertion, deletion, or substitution of a single 
 * character.
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.21CEAA91-6CA4-0FB2-CE37-1A7888D7BC32]
// </editor-fold> 
public class OysterEditDistance {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.AD7E03BD-D055-E30F-9098-BD431FA669FC]
    // </editor-fold> 
    /** The calculated distance between the two strings */
    private int distance = 0;

    /** The length of the longer string */
    private int lengthOfLong = 0;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.EB0B76BB-380F-07BF-808D-2C53085A75EE]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>OysterEditDistance</code>
     */
    public OysterEditDistance () {
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.CA212EA4-FAEF-39C9-62A4-6690A025FAC6]
    // </editor-fold> 
    /**
     * Levenshtein Distance
     * @param s source String
     * @param t target String
     * @return 0 if the strings are exact match, otherwise the number of 
     * transpostions to change String s to String t
     */
    public int computeDistance(String s, String t) {
        int result = 0, cost;
        if (s == null && t != null){
            lengthOfLong = t.length();
            result = t.length();
        } else if (s != null && t == null){
            lengthOfLong = s.length();
            result = s.length();
        } else if (s != null && t != null){
            String sTemp = s.toUpperCase(Locale.US);
            String tTemp = t.toUpperCase(Locale.US);
            
            lengthOfLong = Math.max(sTemp.length(), tTemp.length());
            int m = sTemp.length()+1;
            int n = tTemp.length()+1;
            
            // d is a table with m+1 rows and n+1 columns
            int [][] d = new int[m][n];
            
            for (int i = 0; i < m; i++) {
                d[i][0] = i;
            }
            for (int j = 0; j < n; j++) {
                d[0][j] = j;
            }
            
            for (int j = 1; j < n; j++){
                for (int i = 1; i < m; i++) {
                    if (sTemp.charAt(i-1) == tTemp.charAt(j-1)) {
                        cost = 0;
                    } else {
                        cost = 1;
                    }
                    d[i][j] = Math.min(Math.min(d[i-1][j] + 1,     // insertion
                                                d[i][j-1] + 1),    // deletion
                                                d[i-1][j-1] + cost // substitution
                              );
                }
            }
            result = d[m-1][n-1];
        }
        distance = result;
        return result;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.99EB75B5-7D66-6AEA-169D-59CD98076423]
    // </editor-fold> 
    /** This method computes the normalized edit distance as ratio of edit 
     *  distance to shorter string length
     * @return float as the normalized distance of the two strings being compared
     */
    public float computeNormalizedScore () {
        float norm;
        
        float maxLen = lengthOfLong;
        norm = 1f - ((float) distance / maxLen);
        
        return norm;
    }
    
    /**
     * @param args the command line arguments
     */
/*
    public static void main(String[] args) {
        String s, t;
        OysterEditDistance ed = new OysterEditDistance();
        s = "CRUSAN"; t = "CHRZAN";
        System.out.format("%1$,6d %2$,6.5f %3$s %4$s%n", ed.computeDistance(s, t), ed.computeNormalizedScore(), s, t);
        
        s = "ISLE"; t = "ISELEY";
        System.out.format("%1$,6d %2$,6.5f %3$s %4$s%n", ed.computeDistance(s, t), ed.computeNormalizedScore(), s, t);
        
        s = "PENNING"; t = "PENINGTON";
        System.out.format("%1$,6d %2$,6.5f %3$s %4$s%n", ed.computeDistance(s, t), ed.computeNormalizedScore(), s, t);
        
        s = "PENNINGTON"; t = "PENINGTON";
        System.out.format("%1$,6d %2$,6.5f %3$s %4$s%n", ed.computeDistance(s, t), ed.computeNormalizedScore(), s, t);
        
        s = "STROHMAN"; t = "STROHM";
        System.out.format("%1$,6d %2$,6.5f %3$s %4$s%n", ed.computeDistance(s, t), ed.computeNormalizedScore(), s, t);
        
        s = "EDUARDO"; t = "EDWARD";
        System.out.format("%1$,6d %2$,6.5f %3$s %4$s%n", ed.computeDistance(s, t), ed.computeNormalizedScore(), s, t);
        
        s = "JOHNSON"; t = "JAMISON";
        System.out.format("%1$,6d %2$,6.5f %3$s %4$s%n", ed.computeDistance(s, t), ed.computeNormalizedScore(), s, t);
        
        s = "RAPHAEL"; t = "RAFAEL";
        System.out.format("%1$,6d %2$,6.5f %3$s %4$s%n", ed.computeDistance(s, t), ed.computeNormalizedScore(), s, t);
        
        s = "Eric"; t = null;
        System.out.format("%1$,6d %2$,6.5f %3$s %4$s%n", ed.computeDistance(s, t), ed.computeNormalizedScore(), s, t);
    }
*/
}

