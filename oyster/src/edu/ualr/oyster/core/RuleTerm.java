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

package edu.ualr.oyster.core;

import java.util.Set;

/**
 * RuleTerm.java
 * Created on Mar 29, 2012 7:37:16 PM
 * @author Eric D. Nelson
 */
public class RuleTerm {
    private String item =  null;
    private Set<String> compareTo = null;
    private String matchResult = null;
    
    /**
     * Creates a new instance of RuleTerm
     */
    public RuleTerm(){
    }

    public String getItem() {
        return item;
    }

    public void setItem(String item) {
        this.item = item;
    }

    public Set<String> getCompareTo() {
        return compareTo;
    }

    public void setCompareTo(Set<String> compareTo) {
        this.compareTo = compareTo;
    }

    public String getMatchResult() {
        return matchResult;
    }

    public void setMatchResult(String matchResult) {
        this.matchResult = matchResult;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final RuleTerm other = (RuleTerm) obj;
        if (this.item == null || !this.item.equals(other.item)) {
            return false;
        }
        if (this.compareTo == null || !this.compareTo.equals(other.compareTo)) {
            return false;
        }
        if (this.matchResult == null || !this.matchResult.equals(other.matchResult)) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 17 * hash + (this.item != null ? this.item.hashCode() : 0);
        hash = 17 * hash + (this.compareTo != null ? this.compareTo.hashCode() : 0);
        hash = 17 * hash + (this.matchResult != null ? this.matchResult.hashCode() : 0);
        return hash;
    }
    
    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();
        sb.append(getClass().getName());
        sb.append("[item=");
        sb.append(this.item != null ? this.item : "");
        sb.append(", secItem=");
        sb.append(this.compareTo != null ? this.compareTo : "");
        sb.append(", matchResult=");
        sb.append(this.matchResult != null ? this.matchResult : "");
        sb.append("]");
        return sb.toString();
    }
}
