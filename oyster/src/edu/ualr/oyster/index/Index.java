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

package edu.ualr.oyster.index;

import edu.ualr.oyster.data.ClusterRecord;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * Reduce the number candidate identities that could match a reference to a 
 * manageable number Responsibilities:
 * <ul>
 * <li>Allows other objects to request a list of OysterIdentity objects that 
 * have attributes with a specific value</li>
 * </ul>
 * @author Eric D. Nelson
 */

public interface Index {
    /**
     * Add an entry to the <code>Index</code>.
     * @param key the entry to be added.
     */
    void addEntry (Object key);

    /**
     * Add an entry to the <code>InvertedIndex</code>.
     * @param i the index value to set the reference items to.
     * @param obj the entry to be added.
     */
    public void addEntry(String i, Object obj);
    
    /**
     * Associates the specified value with the specified key in this <code>Index</code>.
     * If the <code>Index</code> previously contained a mapping for this key, 
     * the old value is replaced by the specified value. 
     * @param key the key with which the specified value is to be associated.
     * @param value the value to be associated with the specified key.
     */
    void add(String key, Object value);
    
    /**
     * Associates the specified value with the specified key in this <code>Index</code>.
     * If the <code>Index</code> previously contained a mapping for this key, 
     * the old value is replaced by the specified value. 
     * @param key the key with which the specified value is to be associated.
     * @param value the value to be associated with the specified key.
     */
    void setEntryAt (Object key, String value);

    /**
     * Removes the mapping for this key from this <code>Index</code> if it is present.
     * @param o the Object to be removed.
     */
    void removeEntry (Object o);

    /**
     * Remove the value from the Object in the <code>Index</code>.
     * @param o the Object to be searched.
     * @param value the value to be removed from the Object.
     */
    void removeEntry (Object o, String value);
    
    /**
     * Removes all of the elements from this <code>Index</code>. The <code>Index
     * </code> will be empty after this call returns.
     */
    void clear();
    
    /**
     * Returns the size of the index.
     * @return the size of the index.
     */
    int size();
    
    /**
     * Returns the value to which this <code>Index</code> maps the specified key.
     * Returns null if the <code>Index</code> contains no mapping for this key. 
     * A return value of null does not necessarily indicate that the <code>Index</code>
     * contains no mapping for the key; it's also possible that the <code>Index</code>
     * explicitly maps the key to null.
     * @param key the key to be searched for.
     * @return the value Object specified by the key if it exist, otherwise null.
     */
    Object get(Object key);
    
    /**
     * Returns an iterator over the elements in this <code>Index</code>. The 
     * elements are returned in no particular order (unless this set is an 
     * instance of some class that provides a guarantee). 
     * @return an iterator over the elements in this <code>Index</code>.
     */
    Iterator getIterator();

    /**
     * Returns the passThruAttributes for this <code>OysterIdentityRepository</code>.
     * @return the passThruAttributes.
     */
    public Set<String> getPassThruAttributes();

    /**
     * Sets the passThruAttributes for this <code>OysterIdentityRepository</code>.
     * @param passThruAttributes the passThruAttributes to be set.
     */
    public void setPassThruAttributes(Set<String> passThruAttributes);

    public Set<String> getCandidateList(ClusterRecord clusterRecord, Map<Integer, ArrayList<String>> lcrd, boolean mergedList);

    public String indexStats();
}
