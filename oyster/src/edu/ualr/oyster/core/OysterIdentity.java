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

import java.util.ArrayList; 

/**
 * 
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.057FFEAF-2B9E-BF41-8F4C-9C174F6B143B]
// </editor-fold> 
public class OysterIdentity {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.4DA905F4-9D1C-553C-9FBB-48CED7926A6B]
    // </editor-fold> 
    private String idValue;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.0EE9FE38-3675-0728-3CC2-0567567FAB95]
    // </editor-fold> 
    private String label;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.31DD6B99-6EC3-A5AD-BC6A-EB3816B86375]
    // </editor-fold> 
    private ArrayList<String> valueList;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.79C8D07F-FDA9-23C8-6CF5-DDE87FB96D3C]
    // </editor-fold> 
    private boolean debug = false;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.96FFDA5A-2852-6FDE-0F88-0B014EF66724]
    // </editor-fold> 
    public OysterIdentity () {
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.EE473C15-333F-8A1F-4646-569DF96CD90A]
    // </editor-fold> 
    public String getIdValue () {
        return idValue;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.C9542EAD-CAE2-E361-B5DD-CEFF86973A04]
    // </editor-fold> 
    public void setIdValue (String idValue) {
        this.idValue = idValue;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.82635671-06F3-23C3-90A3-900ED66CEC2D]
    // </editor-fold> 
    public String getLabel () {
        return label;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.4494A3AE-B842-511F-15BA-D70EEDCA3877]
    // </editor-fold> 
    public void setLabel (String label) {
        this.label = label;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.5294944E-88DC-0680-740F-62E3BC0A654C]
    // </editor-fold> 
    public ArrayList<String> getValueList () {
        return valueList;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.645EFC8B-F09B-5728-8D63-3E3826E7B63A]
    // </editor-fold> 
    public void setValueList (ArrayList<String> valueList) {
        this.valueList = valueList;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.BCAE1554-9051-7614-A831-E7754C50C3B8]
    // </editor-fold> 
    public boolean hasLabel (String label) {
        return true;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.7DB194F6-15E4-DBFE-CA59-662E42FBD03F]
    // </editor-fold> 
    public void addNewItemGroup (String label, String value) {
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.6D31744B-B3C2-6F5B-BAA6-CA71CE30F07E]
    // </editor-fold> 
    public void addValueForLabel (String value) {
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.040F31BC-FFA6-ABDC-EA0E-8C337291FC45]
    // </editor-fold> 
    public boolean isDebug () {
        return debug;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.559E8669-F68F-AEE8-E340-46F809A0ABFD]
    // </editor-fold> 
    public void setDebug (boolean debug) {
        this.debug = debug;
    }

}

