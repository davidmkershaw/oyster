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
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * This class represents the Oyster Rule.
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.1A536789-180E-3DBA-F85D-B61C07158A34]
// </editor-fold> 
public class OysterRule {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.24CD675E-610A-2FA4-A492-5BB1CB4F82FB]
    // </editor-fold> 
    /** The attribute term and the associated matchCode */
    private Set<RuleTerm> termList;

    /** The name of this rule */
    private String ruleIdentifer = null;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.9379BF0F-5118-9677-D959-1C77DC1D68B8]
    // </editor-fold> 
    /** */
    private boolean debug = false;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.B7876D31-97FF-D4BE-4EDC-5B27C8D1ECDC]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>OysterRule</code>.
     */
    public OysterRule () {
        termList = new LinkedHashSet<RuleTerm>();
    }

    /**
     * Returns the Rule Identifier for this <code>OysterRule</code>.
     * @return the Rule name.
     */
    public String getRuleIdentifer() {
        return ruleIdentifer;
    }

    /**
     * Sets the Rule Identifier for this <code>OysterRule</code>.
     * @param ruleIdentifer the rule identifier to be set.
     */
    public void setRuleIdentifer(String ruleIdentifer) {
        this.ruleIdentifer = ruleIdentifer;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.2D4C220C-0968-AC19-FF7C-328B8E0637CC]
    // </editor-fold> 
    /**
     * Returns the Term List for this <code>OysterRule</code>.
     * @return the Term List.
     */
    public Set<RuleTerm> getTermList () {
        return termList;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.D5E3B6B3-1B43-640B-C4D2-84C0B53FBA0A]
    // </editor-fold> 
    /**
     * Sets the Term List for this <code>OysterRule</code>.
     * @param termList
     */
    public void setTermList (Set<RuleTerm> termList) {
        this.termList = termList;
    }

    /**
     * Adds the specified item and match result to this map, increasing its size
     * by one.
     * @param rt
     */
    public void insertTerm(RuleTerm rt){
        termList.add(rt);
    }

    /**
     * Adds the specified item and match result to this map, increasing its size
     * by one.
     * @param item
     * @param matchResult
     */
    public void insertTerm(String item, String matchResult){
        RuleTerm rt = new RuleTerm();
        rt.setItem(item);
        rt.setMatchResult(matchResult);
        termList.add(rt);
    }
    
    /**
     * Adds the specified item and match result to this map, increasing its size
     * by one.
     * @param item
     * @param compareTo
     * @param matchResult
     */
    public void insertTerm(String item, Set<String> compareTo, String matchResult){
        RuleTerm rt = new RuleTerm();
        rt.setItem(item);
        rt.setCompareTo(compareTo);
        rt.setMatchResult(matchResult);
        termList.add(rt);
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.8BE910AC-6E41-6E7E-4B6A-2F0935EC9940]
    // </editor-fold> 
    // FIXME: Do I really need this method? 
    public String getTermltemName (int index) {
        return null;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.132B1844-E130-C015-3193-C0A1B9EFD553]
    // </editor-fold> 
    // FIXME: Do I really need this method? 
    public ArrayList<String> getListOfMatchCodes (int index) {
        return null;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.94711AF2-374D-E086-2906-81828D691AD0]
    // </editor-fold> 
    /**
     * Returns whether the <code>OysterRule</code> is in debug mode.
     * @return true if the <code>OysterRule</code> is in debug mode, otherwise false.
     */
    public boolean isDebug () {
        return debug;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.96A6C344-8D05-E66D-94A8-9D240681EFEF]
    // </editor-fold> 
    /**
     * Enables/disables debug mode for the <code>OysterRule</code>.
     * @param debug true to enable debug mode, false to disable it.
     */
    public void setDebug (boolean debug) {
        this.debug = debug;
    }

    /**
     * Returns a string representation of the <code>OysterRule</code>.
     * @return  a string representation of this object.
     */
    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();
        sb.append(getClass().getName());
        sb.append("[ruleIdentifer=");
        sb.append(this.ruleIdentifer != null ? this.ruleIdentifer : "");
        sb.append(", termList=");
        sb.append(this.termList != null ? this.termList : "");
        sb.append("]");
        return sb.toString();
    }
}

