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
// #[regen=yes,id=DCE.C103B66C-24DD-40E7-98DA-37C1381F6D2A]
// </editor-fold> 
public class OysterAttribute {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.ED960E0E-FF98-EE27-2556-F6C2E17900BF]
    // </editor-fold> 
    /** The logical name */
    private String name;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.FA838AC0-BEBF-587C-D571-B672A96D45E6]
    // </editor-fold> 
    /** The String representation of the Comparator class. This should be the 
     *  complete class name starting at the base package. */
    private String algorithm;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.35FFF040-815B-D130-1BE7-60E5F8904650]
    // </editor-fold> 
    /** */
    private boolean debug = false;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.B707A26D-F2F1-9D63-F776-06F37EBD279C]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>OysterAttribute</code>
     */
    public OysterAttribute () {
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.197F381E-4542-6FB8-6A01-81856A78F167]
    // </editor-fold> 
    /**
     * Returns the Algorithm for this Attribute.
     * @return the Algorithm name.
     */
    public String getAlgorithm () {
        return algorithm;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.52D73A2B-47E5-0B67-CD34-FA65E04AB8E4]
    // </editor-fold> 
    /**
     * Set the Algorithm name.
     * @param algorithm the name of the Algorithm to be set.
     */
    public void setAlgorithm (String algorithm) {
        this.algorithm = algorithm;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.D2E0A4F0-64B0-3462-66DB-252FF208A92F]
    // </editor-fold> 
    /**
     * Returns the Attribute name as a String.
     * @return the Attribute name
     */
    public String getName () {
        return name;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.3E899D42-A3D5-B120-3ACC-9BB75EEB30F1]
    // </editor-fold> 
    /**
     * Sets the name of the Attribute
     * @param name the Attribute name to be set
     */
    public void setName (String name) {
        this.name = name;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.9CA2A064-E7E4-BB99-262E-23F5E081EAA3]
    // </editor-fold> 
    /**
     * Returns whether the <code>OysterAttribute</code> is in debug mode.
     * @return true if the <code>OysterAttribute</code> is in debug mode, otherwise false.
     */
    public boolean isDebug () {
        return debug;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.364FD713-4708-1396-736D-4C4E3E2DA05A]
    // </editor-fold> 
    /**
     * Enables/disables debug mode for the <code>OysterAttribute</code>.
     * @param debug true to enable debug mode, false to disable it.
     */
    public void setDebug (boolean debug) {
        this.debug = debug;
    }

    /**
     * Returns a hash code value for the <code>OysterAttribute</code>.
     * @return a hash code value for this object.
     */
    @Override
    public int hashCode() {
        int hash = 5;
        hash = 31 * hash + (this.name != null ? this.name.hashCode() : 0);
        hash = 31 * hash + (this.algorithm != null ? this.algorithm.hashCode() : 0);
        return hash;
    }

    /**
     * Determines of this object is equal to another object.
     * @param obj the reference object with which to compare. 
     * @return true if this object is the same as the obj argument; false otherwise.
     */
    @Override
    public boolean equals(Object obj) {
        boolean flag = true;
        if (obj == null) {
            flag = false;
        } else if (getClass() != obj.getClass()) {
            flag = false;
        } else {
            final OysterAttribute other = (OysterAttribute) obj;
            // FIXME: See TraceRecord
            if (other == null) {
                flag = false;
            } else if (this.name != null && other.name != null && !this.name.equalsIgnoreCase(other.name)) {
                flag = false;
            } else if (this.algorithm != null && other.algorithm != null && !this.algorithm.equalsIgnoreCase(other.algorithm)) {
                flag = false;
            }
        }
        return flag;
    }
    
    /**
     * Returns a String representation of the <code>OysterAttribute</code> object
     * @return a String
     */
    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();
        sb.append(getClass().getName());
        sb.append("[");
        sb.append("name=").append(name);
        sb.append(", algorithm=").append(algorithm);
        sb.append("]");
        return sb.toString();
    }
}

