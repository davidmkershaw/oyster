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

import java.util.logging.Formatter;
import java.util.logging.LogRecord;


/**
 * This class is used to format the Oyster Explantion to a string so that it can
 * be output by the <code>Logger</code>.
 * Created on Jul 25, 2010
 * @author Eric D. Nelson
 */
public class OysterExplanationFormatter extends Formatter {
    /**
     * Creates a new instance of OysterExplanationFormatter
     */
    public OysterExplanationFormatter(){
    }

    /**
     * Formats the LogRecord to a string that is used by the <code>Logger</code>
     * @param rec the <code>LogRecord</code> to be formated
     * @return the <code>LogRecord</code> as a string.
     */
    @Override
    public String format(LogRecord rec) {
        StringBuilder sb = new StringBuilder(1000);
        sb.append(formatMessage(rec));
        sb.append(System.getProperty("line.separator"));
        return sb.toString();

    }
}
