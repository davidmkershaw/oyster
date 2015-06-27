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

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Locale;
import java.util.Set;

/**
 * This class computes Tanimoto coefficient between the characters in the two 
 * strings. Strings that have Tanimoto coefficient values > 0.85 are generally
 * considered similar to each other.
 * 
 * Created on Jul 8, 2012 1:48:40 AM
 * @author Eric D. Nelson
 */
public class Tanimoto {
    /**
     * Creates a new instance of Tanimoto
     */
    public Tanimoto(){
    }

    public float computeDistance(String s, String t) {
        float distance = 0;
        int c1 = 0, c2 = 0, c3 = 0;
        Set<Character> set = new LinkedHashSet<Character>();
        String sTemp = "", tTemp = "";
        
        if (s == null && t != null){
            tTemp = t.toUpperCase(Locale.US);
            for (int i = 0; i < tTemp.length(); i++) {
                set.add(tTemp.charAt(i));
            }
        }
        else if (s != null && t == null){
            sTemp = s.toUpperCase(Locale.US);
            for (int i = 0; i < sTemp.length(); i++) {
                set.add(sTemp.charAt(i));
            }
        }
        else if (s != null && t != null){
            sTemp = s.toUpperCase(Locale.US);
            tTemp = t.toUpperCase(Locale.US);
            
            for (int i = 0; i < tTemp.length(); i++) {
                set.add(tTemp.charAt(i));
            }
            
            for (int i = 0; i < sTemp.length(); i++) {
                set.add(sTemp.charAt(i));
            }
        }
        
        for (Iterator<Character> it = set.iterator(); it.hasNext();){
            Character c = it.next();
            
            if (sTemp.contains(String.valueOf(c))) {
                c1++;
            }
            
            if (tTemp.contains(String.valueOf(c))) {
                c2++;
            }
            
            if (sTemp.contains(String.valueOf(c)) && tTemp.contains(String.valueOf(c))) {
                c3++;
            }
        }
        
        if (c3 > 0) {
            distance = (float)c3/(float)(c1+c2-c3);
        }
        return distance;
    }

    /**
     * @param args the command line arguments
     */
/*
    public static void main(String[] args) {
        String s, t;
        Tanimoto j = new Tanimoto();
        s = "CRUSAN"; t = "CHRZAN";
        System.out.format("%1$,6.5f %2$s %3$s%n", j.computeDistance(s, t), s, t);
        
        s = "ISLE"; t = "ISELEY";
        System.out.format("%1$,6.5f %2$s %3$s%n", j.computeDistance(s, t), s, t);
        
        s = "PENNING"; t = "PENINGTON";
        System.out.format("%1$,6.5f %2$s %3$s%n", j.computeDistance(s, t), s, t);
        
        s = "PENNINGTON"; t = "PENINGTON";
        System.out.format("%1$,6.5f %2$s %3$s%n", j.computeDistance(s, t), s, t);
        
        s = "STROHMAN"; t = "STROHM";
        System.out.format("%1$,6.5f %2$s %3$s%n", j.computeDistance(s, t), s, t);
        
        s = "EDUARDO"; t = "EDWARD";
        System.out.format("%1$,6.5f %2$s %3$s%n", j.computeDistance(s, t), s, t);
        
        s = "JOHNSON"; t = "JAMISON";
        System.out.format("%1$,6.5f %2$s %3$s%n", j.computeDistance(s, t), s, t);
        
        s = "RAPHAEL"; t = "RAFAEL";
        System.out.format("%1$,6.5f %2$s %3$s%n", j.computeDistance(s, t), s, t);
        
        s = "Eric"; t = null;
        System.out.format("%1$,6.5f %2$s %3$s%n", j.computeDistance(s, t), s, t);
    }
*/
}
