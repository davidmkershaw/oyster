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

import java.util.LinkedHashSet;
import java.util.Locale;
import java.util.Set;

/**
 * This class computes Jaccard distance between the characters in the two 
 * strings. The Jaccard coefficient measures similarity between sample sets, and
 * is defined as the size of the intersection divided by the size of the union.
 * 
 * Created on Jul 8, 2012 1:48:40 AM
 * @author Eric D. Nelson
 */
public class Jaccard {
    /**
     * Creates a new instance of Jaccard
     */
    public Jaccard(){
    }

    public float computeDistance(String s, String t) {
        float distance = 0;
        Set<Character> sSet = new LinkedHashSet<Character>();
        Set<Character> tSet = new LinkedHashSet<Character>();
        
        if (s == null && t != null){
            String tTemp = t.toUpperCase(Locale.US);
            for (int i = 0; i < tTemp.length(); i++) {
                tSet.add(tTemp.charAt(i));
            }
        } else if (s != null && t == null){
            String sTemp = s.toUpperCase(Locale.US);
            for (int i = 0; i < sTemp.length(); i++) {
                sSet.add(sTemp.charAt(i));
            }
        } else if (s != null && t != null){
            String sTemp = s.toUpperCase(Locale.US);
            String tTemp = t.toUpperCase(Locale.US);
            
            for (int i = 0; i < tTemp.length(); i++) {
                tSet.add(tTemp.charAt(i));
            }
            
            for (int i = 0; i < sTemp.length(); i++) {
                sSet.add(sTemp.charAt(i));
            }
        }
        
        Set intersection = getIntersection(sSet, tSet);
        Set union = getUnion(sSet, tSet);
        
        if (!union.isEmpty()) {
            distance = (float)intersection.size()/(float)union.size();
        }
        return distance;
    }

    private Set getIntersection(Set<Character> sSet, Set<Character> tSet) {
        Set<Character> set = new LinkedHashSet<Character>();
        
        if (sSet.size() > tSet.size()){
            set.addAll(sSet);
            set.retainAll(tSet);
        } else {
            set.addAll(tSet);
            set.retainAll(sSet);
        }
        
        return set;
    }

    private Set getUnion(Set<Character> sSet, Set<Character> tSet) {
        Set<Character> set = new LinkedHashSet<Character>();
        set.addAll(sSet);
        set.addAll(tSet);
        return set;
    }

    /**
     * @param args the command line arguments
     */
/*
    public static void main(String[] args) {
        String s, t;
        Jaccard j = new Jaccard();
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
