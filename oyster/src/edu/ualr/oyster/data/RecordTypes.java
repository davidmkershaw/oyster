/*
 * Copyright 2012 John Talburt, Eric Nelson
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

package edu.ualr.oyster.data;

/**
 * RecordTypes.java
 * Created on Sep 20, 2011 12:05:00 PM
 * @author Eric D. Nelson
 */
public class RecordTypes {
    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the generic Record type 
    * <code>CODOSA</code>.
    */
    public final static int CODOSA 		=  -110000;
    
    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the generic Record type 
    * <code>MAP</code>.
    */
    public final static int MAP 		=  -120000;
    
    /**
     * Creates a new instance of ERTypes
     */
    // Prevent instantiation
    private RecordTypes(){
    }
}
