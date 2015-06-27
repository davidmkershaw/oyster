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

import edu.ualr.oyster.data.ClusterRecord;
import edu.ualr.oyster.data.OysterIdentityRecord;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * This class is used as a null index. It returns everything that has been seen
 * up to the time of the request.
 * 
 * Created on Jun 9, 2012 12:40:36 AM
 * @author Eric D. Nelson
 */
public class NullIndex extends InvertedIndex {
    private String hash = "<null>";
    
    /**
     * Creates a new instance of NullIndex
     */
    public NullIndex(){
        super();
    }

    /**
     * Add an entry to the <code>NullIndex</code>.
     * @param obj the entry to be added.
     */
    @Override
    public void addEntry(Object obj) {
        if (obj != null) {
            OysterIdentityRecord oir = (OysterIdentityRecord) obj;

            // get the RefID
            String value = oir.get("@RefID");
            Set<String> s = index.get(hash);

            if (s == null) {
                s = new LinkedHashSet<String>();
            }

            s.add(value);
            index.put(hash, s);
        }
    }

    /**
     * Add an entry to the <code>NullIndex</code>.
     * @param refID the refID to set the reference items to.
     * @param obj the entry to be added.
     */
    @Override
    public void addEntry(String refID, Object obj) {
        if (obj != null) {
            Set<String> s = index.get(hash);

            if (s == null) {
                s = new LinkedHashSet<String>();
            }

            s.add(refID);
            index.put(hash, s);
        }
    }
    
    /**
     * Associates the specified value with the specified key in this <code>
     * NullIndex</code>. If the <code>NullIndex</code> previously contained a 
     * mapping for this key, the old value is replaced by the specified value. 
     * @param key the key with which the specified value is to be associated.
     * @param o the value to be associated with the specified key.
     */
    @SuppressWarnings( "unchecked" )
    @Override
    public void add(String key, Object o){
        Set<String> s = index.get(hash);
        Set<String> set = (Set<String>) o;
        if (s != null) {
            s.addAll(set);
            
            index.put(hash, s);
        }
        else {
            index.put(hash, set);
        }
    }
    
    /**
     * Associates the specified value with the specified key in this <code>
     * NullIndex</code>. If the <code>NullIndex</code> previously contained a 
     * mapping for this key, the old value is replaced by the specified value. 
     * @param key the key with which the specified value is to be associated.
     * @param value the value to be associated with the specified key.
     */
    @Override
    public void setEntryAt(Object key, String value) {
        OysterIdentityRecord oir = (OysterIdentityRecord) key;
        
        if (oir != null) {
            Set<String> s = index.get(hash);

            if (s == null) {
                s = new LinkedHashSet<String>();
            }

            s.add(value);
            index.put(hash, s);
        }
    }

    /**
     * Removes the mapping for this key from this <code>NullIndex
     * </code> if it is present.
     * @param obj the Object to be removed.
     */
    @Override
    public void removeEntry (Object obj) {
        
    }

    /**
     * Remove the refID from the Object in the <code>NullIndex</code>.
     * @param obj the Object to be searched.
     * @param refID the refID to be removed from the Object.
     */
    @Override
    public void removeEntry(Object obj, String refID) {
        
    }

    @SuppressWarnings( "unchecked" )
    @Override
    public Set<String> getCandidateList(ClusterRecord clusterRecord, Map<Integer, ArrayList<String>> lcrd, boolean mergedList) {        
        Set<String> candidates = new HashSet<String>();

        Set<String> s = index.get(hash);
        
        if (s == null) {
            s = new HashSet<String>();
        }
        
        for (Iterator<String> it = s.iterator(); it.hasNext();) {
            candidates.add(it.next());
        }

        return candidates;
    }
}
