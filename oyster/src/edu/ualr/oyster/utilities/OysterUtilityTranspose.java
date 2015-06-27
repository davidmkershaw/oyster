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

/**
 * This class determines if a source and target are equivalent. if they have at 
 * most one adjacent char that is swapped. i.e. John ≈ Jonh
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.F7B01291-DA4B-C60B-D1C9-228612A854A1]
// </editor-fold> 
public class OysterUtilityTranspose {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.EA0DB467-1B6B-39E2-2D35-973EE440B192]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>OysterUtilityTranspose</code>
     */
    public OysterUtilityTranspose () {
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.BF6669EA-CECD-9A52-A951-D46A3BD785CD]
    // </editor-fold> 
    /**
     * One string differs from the other string by only one adjacent transposition (John - Jhon)
     * @param s source String
     * @param t target String
     * @return true if single position transpose, otherwise false
     */
    public boolean differByTranspose (String s, String t) {
        boolean flag = false;
        if (s == null && t == null) {
            flag = false;
        } else if (s != null && t == null) {
            flag = false;
        } else if (s == null && t != null) {
            flag = false;
        } else {
            int distance = 0, first = 0, second = 0;
            int len = Math.min(s.length(), t.length());
            boolean firstFound = false;

            for (int i = 0; i < len; i++) {
                if (s.charAt(i) != t.charAt(i)) {
                    if (!firstFound) {
                        first = i;
                    } else {
                        second = i;
                    }
                    distance++;
                    firstFound = true;
                }
            }

            if (distance == 2) { // only one transposition
                if (first + 1 == second) { // must be adjacent
                    if (s.charAt(first) == t.charAt(second) &&
                        s.charAt(second) == t.charAt(first)) {
                        flag = true;
                    }
                }
            }
        }
        return flag;
    }

}

