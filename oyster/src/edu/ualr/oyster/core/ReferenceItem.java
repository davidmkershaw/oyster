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

/**
 * 
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.B09A548C-8FCF-56D4-1E80-18181FF77534]
// </editor-fold> 
public class ReferenceItem {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.9964324E-A11A-26EF-E81F-45B9FF047982]
    // </editor-fold> 
    /** The Physical Name */
    private String name = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.13FC476E-8161-4823-41B2-47DC8B619010]
    // </editor-fold> 
    /** The Logical Name */
    private String attribute = null;

    /** 
     * Used for database retrieval of data that can have multiple formats, i.e.
     * dates.
     */
    private String format = null;
    
    /** The actual type of data that is to be formated, i.e. Date */
    private String formatType = null;
    
    /** The data starting index */
    private int start = 0;
    
    /** The data ending index */
    private int end = 0;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.3948DB3B-2AB1-2C76-1108-33734F2FCDFF]
    // </editor-fold> 
    /** The data position */
    private int ordinal = -1;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.7DAFBC1B-11DC-F7A5-E41C-2C55FFCE7C26]
    // </editor-fold> 
    /** The data */
    private String data = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.96E23F12-949E-66B0-E275-981652F1F1DC]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>ReferenceItem</code>.
     */
    public ReferenceItem() {
    }

    /**
     * Creates a new instance of <code>ReferenceItem</code>.
     * @param name the physical name to be set
     * @param attribute the logical name to be set
     */
    public ReferenceItem(String name, String attribute) {
        this.name = name;
        this.attribute = attribute;
    }
    
    /**
     * Creates a new instance of <code>ReferenceItem</code>.
     * @param name the physical name to be set
     * @param attribute the logical name to be set
     * @param pos the data position to be set
     */
    public ReferenceItem(String name, String attribute, int pos) {
        this.name = name;
        this.attribute = attribute;
        this.ordinal = pos;
    }
    
    /**
     * Creates a new instance of <code>ReferenceItem</code>.
     * @param name the physical name to be set
     * @param attribute the logical name to be set
     * @param start the starting index to start
     * @param end the ending index to be set
     */
    public ReferenceItem(String name, String attribute, int start, int end) {
        this.name = name;
        this.attribute = attribute;
        this.start = start;
        this.end = end;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.77674689-375D-10F0-420D-73325334F4FA]
    // </editor-fold> 
    /**
     * Returns the Name for this <code>ReferenceItem</code>.
     * @return the Name.
     */
    public String getName () {
        return name;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.78BA37C6-7CDF-4CDE-85BD-782F23CE720B]
    // </editor-fold> 
    /**
     * Sets the Name for this <code>ReferenceItem</code>.
     * @param name the Name to be set.
     */
    public void setName (String name) {
        this.name = name;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.F309C7A9-BFDD-A2EF-E6CB-9F044B8F00EC]
    // </editor-fold> 
    /**
     * Returns the Attribute name for this <code>ReferenceItem</code>.
     * @return the Attribute name.
     */
    public String getAttribute() {
        return attribute;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.58350028-1CCC-766B-FBF0-880339A038DE]
    // </editor-fold> 
    /**
     * Sets the Attribute name for this <code>ReferenceItem</code>.
     * @param attribute the Attribute name to be set.
     */
    public void setAttribute (String attribute) {
        this.attribute = attribute;
    }

    /**
     * Returns the Attribute format for this <code>ReferenceItem</code>.
     * @return the Attribute format.
     */
    public String getFormat() {
        return format;
    }

    /**
     * Sets the Attribute format for this <code>ReferenceItem</code>.
     * @param format the Attribute format to be set
     */
    public void setFormat(String format) {
        this.format = format;
    }
    
    /**
     * Returns the Attribute formatType for this <code>ReferenceItem</code>
     * @return the Attribute formatType.
     */
    public String getFormatType() {
        return formatType;
    }

    /**
     * Sets the Attribute formatType for this <code>ReferenceItem</code>.
     * @param formatType the Attribute formatType to be set.
     */
    public void setFormatType(String formatType) {
        this.formatType = formatType;
    }

    /**
     * Returns the Starting position for this <code>ReferenceItem</code>.
     * @return the Starting position.
     */
    public int getStart() {
        return start;
    }

    /**
     * Sets the Starting position for this <code>ReferenceItem</code>.
     * @param start the Starting position to be set.
     */
    public void setStart(int start) {
        this.start = start;
    }

    /**
     * Returns the End position for this <code>ReferenceItem</code>.
     * @return the End position.
     */
    public int getEnd() {
        return end;
    }

    /**
     * Sets the End position for this <code>ReferenceItem</code>.
     * @param end the End position to be set.
     */
    public void setEnd(int end) {
        this.end = end;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.EDAA82B1-3920-ABFB-6F58-12939A57870E]
    // </editor-fold> 
    /**
     * Returns the Ordinal for this <code>ReferenceItem</code>.
     * @return the Ordinal
     */
    public int getOrdinal () {
        return ordinal;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.25E4BAFA-1B47-A44A-FA4B-E4B371E9D061]
    // </editor-fold> 
    /**
     * Sets the Ordinal for this <code>ReferenceItem</code>.
     * @param ordinal the Ordinal to be set.
     */
    public void setOrdinal (int ordinal) {
        this.ordinal = ordinal;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.E8453348-B92D-384C-6718-80682FB7DBEE]
    // </editor-fold> 
    /**
     * Returns the Data value for this <code>ReferenceItem</code>.
     * @return the Data value.
     */
    public String getData () {
        return data;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.76565A0A-2EEE-754A-3246-0362B27F7B43]
    // </editor-fold> 
    /**
     * Sets the Data value for this <code>ReferenceItem</code>.
     * @param data the Data value to be set.
     */
    public void setData (String data) {
        if (data != null) {
            this.data = data;
        }
    }
    
    @Override
    /**
     * Returns a String representation of the <code>ReferenceItem</code> data.
     * @return
     */
    public String toString(){
        return data;
    }
}

