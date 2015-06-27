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

package edu.ualr.oyster.core;

import java.io.Serializable;
import java.util.Comparator;

/**
 * OysterAttributeComparator.java
 * 
 * Used to compare Oyster Attributes in Collections.
 * 
 * Created on Oct 24, 2010 12:16:43 AM
 * @author Eric D. Nelson
 */
public class OysterAttributeComparator implements Comparator<OysterAttribute>, Serializable{
    private static final long serialVersionUID = 122387467;
    
    /**
     * Creates a new instance of OysterAttributeComparator
     */
    public OysterAttributeComparator(){
    }

    /**
     * Get the value of serialVersionUID
     *
     * @return the value of serialVersionUID
     */
    public static long getSerialVersionUID() {
        return serialVersionUID;
    }

    /**
     * Compares two <code>OysterAttribute</code> based on the String comparisons
     * of OysterAttribute.name and OysterAttribute.algorithm. If both sub-elements
     * are equal will return 0. If either sub-element is not equal but the sum
     * of sub-elements comparison equals zero then -1 is returned, else the sum 
     * of the sub-elements comparison is returned.
     * @param oa1 the first <code>OysterAttribute</code> to be compared.
     * @param oa2 the second <code>OysterAttribute</code> to be compared.
     * @return the value <code>0</code> if the <code>OysterAttribute</code> are
     *         equal; a value less than <code>0</code> if they are not; and a
     *         value greater than <code>0</code> if they are greater than the 
     *         string argument.
     */
    @Override
    public int compare(OysterAttribute oa1, OysterAttribute oa2) {
        int result;
        if (oa1.getName().equalsIgnoreCase(oa2.getName()) &&
            oa1.getAlgorithm().equalsIgnoreCase(oa2.getAlgorithm())){
            result = 0;
        } else if (!oa1.getName().equalsIgnoreCase(oa2.getName()) ||
                 !oa1.getAlgorithm().equalsIgnoreCase(oa2.getAlgorithm()) &&
                 oa1.getName().compareToIgnoreCase(oa2.getName()) +
                 oa1.getAlgorithm().compareToIgnoreCase(oa2.getAlgorithm()) == 0){
            result = -1;
        } else{
            result = oa1.getName().compareToIgnoreCase(oa2.getName()) +
                     oa1.getAlgorithm().compareToIgnoreCase(oa2.getAlgorithm());
        }
        return result;
    }
}
