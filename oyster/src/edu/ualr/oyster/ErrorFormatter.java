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

package edu.ualr.oyster;

/**
 * Formats the Exception message to a string that is used by the <code>Logger
 * </code>
 * Created on Sep 29, 2010 8:38 PM
 * @author Eric D. Nelson
 */
public class ErrorFormatter {
    /**
     * Creates a new instance of ErrorFormatter
     */
    public ErrorFormatter(){
    }

    /**
     * Formats the Exception message to a string that is used by the <code>Logger
     * </code>
     * @param ex the <code>Exception</code> to be formated
     * @return the <code>Exception</code> as a string.
     */
    public static String format(Exception ex) {
        StringBuilder sb = new StringBuilder(1000);
        StackTraceElement[] ste = ex.getStackTrace();
        
        sb.append("##JAVA: ").append(ex.getMessage()).append(System.getProperty("line.separator"));
        sb.append(ex.toString()).append(System.getProperty("line.separator"));
        for (int i = 0; i < ste.length-1; i++){
            sb.append(ste[i].toString()).append(System.getProperty("line.separator"));
        }
        
        if (ste.length > 0) {
            sb.append(ste[ste.length-1].toString()).append(System.getProperty("line.separator"));
        }
        
        return sb.toString();

    }
}
