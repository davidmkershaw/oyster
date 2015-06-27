/*
 * Copyright 2011 John Talburt, Eric Nelson
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

package edu.ualr.oyster.kb;

/**
 * ModificationRecord.java
 * Created on Apr 30, 2011 11:05:46 PM
 * @author Eric D. Nelson
 */
public class ModificationRecord {
    /** The sequential number assigned for each run */
    private String id = "";
    
    /** The Oyster Version number for this <code>ModificationRecord</code> */
    private String oysterVersion = "";

    /** The date for this <code>ModificationRecord</code> */
    private String date = "";

    /** The runScriptName for this <code>ModificationRecord</code> */
    private String runScriptName = "";
    
    /**
     * Creates a new instance of <code>ModificationRecord</code>
     */
    public ModificationRecord(){
    }

    /**
     * Returns the ID for this <code>ModificationRecord</code>.
     * @return id
     */
    public String getId() {
        return id;
    }

    /**
     * Sets the ID for this <code>ModificationRecord</code>.
     * @param id
     */
    public void setId(String id) {
        this.id = id;
    }

    /**
     * Returns the Oyster Version for this <code>ModificationRecord</code>.
     * @return oysterVersion
     */
    public String getOysterVersion() {
        return oysterVersion;
    }

    /**
     * Sets the Oyster Version for this <code>ModificationRecord</code>.
     * @param oysterVersion
     */
    public void setOysterVersion(String oysterVersion) {
        this.oysterVersion = oysterVersion;
    }

    /**
     * Returns the date for this <code>ModificationRecord</code>.
     * @return date
     */
    public String getDate() {
        return date;
    }

    /**
     * Sets the date for this <code>ModificationRecord</code>.
     * @param date
     */
    public void setDate(String date) {
        this.date = date;
    }

    /**
     * Returns the RunScript Name for this <code>ModificationRecord</code>.
     * @return runScriptName
     */
    public String getRunScriptName() {
        return runScriptName;
    }

    /**
     * Sets the RunScript Name for this <code>ModificationRecord</code>.
     * @param runScriptName
     */
    public void setRunScriptName(String runScriptName) {
        this.runScriptName = runScriptName;
    }
}
