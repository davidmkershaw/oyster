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

package edu.ualr.oyster.index;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * This class represents the Indexing Rule.
 * @author Eric D. Nelson
 */

public class IndexRule {

    /** The attribute term and the associated hash */
    private Map<String, String> segments;

    /** The name of this rule */
    private String ruleIdentifier = null;

    /**
     * Creates a new instance of <code>IndexRule</code>.
     */
    public IndexRule () {
        segments = new LinkedHashMap<String, String>();
    }

    /**
     * Returns the Rule Identifier for this <code>IndexRule</code>.
     * @return the Rule name.
     */
    public String getRuleIdentifier() {
        return ruleIdentifier;
    }

    /**
     * Sets the Rule Identifier for this <code>IndexRule</code>.
     * @param ruleIdentifier the rule identifier to be set.
     */
    public void setRuleIdentifier(String ruleIdentifier) {
        this.ruleIdentifier = ruleIdentifier;
    }

    /**
     * Returns the Segment List for this <code>IndexRule</code>.
     * @return the Segment List.
     */
    public Map<String, String> getSegments () {
        return segments;
    }

    /**
     * Sets the Segment List for this <code>IndexRule</code>.
     * @param segment
     */
    public void setSegments (Map<String, String> segments) {
        this.segments = segments;
    }

    /**
     * Adds the specified item and match result to this map, increasing its size
     * by one.
     * @param item
     * @param matchResult
     */
    public void insertSegment(String item, String matchResult){
         segments.put(item, matchResult);
    }

    /**
     * Returns a string representation of the <code>IndexRule</code>.
     * @return  a string representation of this object.
     */
    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();
        sb.append(getClass().getName());
        sb.append("[ruleIdentifer=");
        sb.append(this.ruleIdentifier != null ? this.ruleIdentifier : "");
        sb.append(", termList=");
        sb.append(this.segments != null ? this.segments : "");
        sb.append("]");
        return sb.toString();
    }
}

