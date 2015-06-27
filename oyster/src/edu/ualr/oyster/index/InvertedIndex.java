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
import edu.ualr.oyster.data.OysterIdentityRecord;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Formatter;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Locale;
import java.util.Map; 
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;

/**
 * An Inverted Index is a mapping structure that maps a word to its location 
 * within the data file. The goal of an inverted index is to optimize the speed 
 * of the query: find the documents where word X occurs [Zobel, J. Moffat, A. 
 * (July 2006). "Inverted Files for Text Search Engines". ACM Computing Surveys 
 * (New York: Association for Computing Machinery) 38 (2): 6]. This simple index
 * allows fast full document search of all reference items that it has read up 
 * to the point of the index query. This index will simply be a map object. The 
 * key will be the reference item (name, DOB, etc) and the value list will be a 
 * collection of sequence numbers. 
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.47CC8817-13E6-2FA6-29A3-1D3DE2906C50]
// </editor-fold> 
abstract public class InvertedIndex implements Index {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.F1C932DB-21AE-9032-65AF-9366DDC94E34]
    // </editor-fold> 
    /** The Index */
    protected Map<String, Set<String>> index;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.F2D90D28-B70C-8A21-7E67-BED44EEE7405]
    // </editor-fold> 
    /** */
    protected boolean debug = false;

    /** The passThruAttributes is used to handle attributes that are not used in
     * the ER process but need to be passed through to the output */
    protected Set<String> passThruAttributes = null;
    
    protected TreeMap<Integer, Integer> candidateList = new TreeMap<Integer, Integer>();
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.1FB65BE1-5D05-9937-B69B-A01347C94336]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>InvertedIndex</code>.
     */
    public InvertedIndex () {
        index = new LinkedHashMap<String, Set<String>>();
        passThruAttributes = new LinkedHashSet<String>();
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.9679824A-1885-BC8E-639B-30CBE6EB2C1A]
    // </editor-fold> 
    /**
     * Returns the index.
     * @return the index.
     */
    public Map<String, Set<String>> getIndex () {
        return index;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.2A63F977-C427-5726-8707-28AA89134317]
    // </editor-fold> 
    /**
     * Sets the index.
     * @param index the index to be set.
     */
    public void setIndex (Map<String, Set<String>> index) {
        this.index = index;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.DFBAD3A9-8002-4BC3-1508-5415434F0811]
    // </editor-fold> 
    /**
     * Returns whether the <code>InvertedIndex</code> is in debug mode.
     * @return true if the <code>InvertedIndex</code> is in debug mode, 
     * otherwise false.
     */
    public boolean isDebug () {
        return debug;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.D2C55D24-1D80-C0A2-D944-467A4EA7A9D4]
    // </editor-fold> 
    /**
     * Enables/disables debug mode for the <code>InvertedIndex</code>.
     * @param debug true to enable debug mode, false to disable it.
     */
    public void setDebug (boolean debug) {
        this.debug = debug;
    }
    
    /**
     * Returns the passThruAttributes for this <code>OysterIdentityRepository</code>.
     * @return the passThruAttributes.
     */
    @Override
    public Set<String> getPassThruAttributes() {
        return passThruAttributes;
    }

    /**
     * Sets the passThruAttributes for this <code>OysterIdentityRepository</code>.
     * @param passThruAttributes the passThruAttributes to be set.
     */
    @Override
    public void setPassThruAttributes(Set<String> passThruAttributes) {
        this.passThruAttributes = passThruAttributes;
    }
    
    /**
     * Returns the size of the index.
     * @return the size of the index.
     */
    @Override
    public int size(){
        int size = -1;
        if (index != null) {
            size = index.size();
        }
        return size;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.A4A21DF5-2638-AB32-8B2B-C59077E869E3]
    // </editor-fold> 
    /**
     * Add an entry to the <code>InvertedIndex</code>.
     * @param obj the entry to be added.
     */
    @Override
    public void addEntry(Object obj) {
        if (obj != null) {
            OysterIdentityRecord oir = (OysterIdentityRecord) obj;

            // get the RefID
            String value = oir.get("@RefID");
            Set<String> hashes = getHash(oir);
            for (Iterator<String> it = hashes.iterator(); it.hasNext();) {
                String hash = it.next();
                Set<String> s = index.get(hash);

                if (s == null) {
                    s = new LinkedHashSet<String>();
                }

                String[] values = value.split("[|]");
                s.addAll(Arrays.asList(values));
                index.put(hash, s);
            }
        } else {
            System.out.println("Null obj insertion into index");
        }
    }

    /**
     * Add an entry to the <code>InvertedIndex</code>.
     * @param refID the refID to set the reference items to.
     * @param obj the entry to be added.
     */
    @Override
    public void addEntry(String refID, Object obj) {
        if (obj != null) {
            OysterIdentityRecord oir = (OysterIdentityRecord) obj;
            Set<String> hashes = getHash(oir);

            for (Iterator<String> it = hashes.iterator(); it.hasNext();) {
                String hash = it.next();
                Set<String> s = index.get(hash);

                if (s == null) {
                    s = new LinkedHashSet<String>();
                }

                s.add(refID);
                index.put(hash, s);
            }
        } else {
            System.out.println("Null obj insertion into index");
        }
    }

    /**
     * Associates the specified value with the specified key in this <code>
     * InvertedIndex</code>. If the <code>InvertedIndex</code> previously 
     * contained a mapping for this key, the old value is replaced by the 
     * specified value. 
     * @param key the key with which the specified value is to be associated.
     * @param o the value to be associated with the specified key.
     */
    @SuppressWarnings( "unchecked")
    @Override
    public void add(String key, Object o) {
        Set<String> s = index.get(key.trim());
        Set<String> set = (Set<String>) o;
        if (s != null) {
            s.addAll(set);

            index.put(key.trim(), s);
        } else {
            index.put(key.trim(), set);
        }
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.1F04FF3E-9A3A-A596-794C-295E406BBEF0]
    // </editor-fold> 
    /**
     * Associates the specified value with the specified key in this <code>
     * InvertedIndex</code>. If the <code>InvertedIndex</code> previously 
     * contained a mapping for this key, the old value is replaced by the 
     * specified value. 
     * @param key the key with which the specified value is to be associated.
     * @param value the value to be associated with the specified key.
     */
    @Override
    public void setEntryAt(Object key, String value) {
        OysterIdentityRecord oir = (OysterIdentityRecord) key;

        if (oir != null) {
            Set<String> hashes = getHash(oir);

            for (Iterator<String> it = hashes.iterator(); it.hasNext();) {
                String hash = it.next();
                Set<String> s = index.get(hash);

                if (s == null) {
                    s = new LinkedHashSet<String>();
                }

                if (!s.contains(value) && !hash.equals("")) {
                    s.add(value);
                    index.put(hash, s);
                }
            }
        } else {
            System.out.println("Null obj insertion into index");
        }
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.7F6CF1CB-180E-EA17-5324-E2B489243371]
    // </editor-fold> 
    /**
     * Removes the mapping for this key from this <code>InvertedIndex</code> if
     * it is present.
     * @param obj the Object to be removed.
     */
    @Override
    public void removeEntry (Object obj) {
        String key = (String) obj;
        index.remove(key);
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.A81CF513-E217-2C68-76DD-E5A32EA128DD]
    // </editor-fold> 
    /**
     * Remove the value from the Object in the <code>InvertedIndex</code>.
     * @param obj the Object to be searched.
     * @param refID the refID to be removed from the Object.
     */
    @Override
    public void removeEntry(Object obj, String refID) {
        OysterIdentityRecord oir = (OysterIdentityRecord) obj;

        if (oir != null) {
            Set<String> hashes = getHash(oir);

            for (Iterator<String> it = hashes.iterator(); it.hasNext();) {
                String hash = it.next();
                Set<String> s = index.get(hash);

                if (s != null) {
                    if (s.contains(refID)) {
                        s.remove(refID);

                        if (s.isEmpty()) {
                            this.index.remove(hash);
                        } else {
                            this.index.put(hash, s);
                        }
                    }
                }
            }
        }
    }

    /**
     * Removes all of the elements from this <code>InvertedIndex</code>. The 
     * <code>InvertedIndex</code> will be empty after this call returns.
     */
    @Override
    public void clear() {
        index.clear();
    }

    /**
     * Returns the value to which this <code>InvertedIndex</code> maps the 
     * specified key. Returns null if the <code>InvertedIndex</code> contains no
     * mapping for this key. A return value of null does not necessarily indicate
     * that the <code>InvertedIndex</code> contains no mapping for the key; 
     * it's also possible that the <code>InvertedIndex</code> explicitly maps 
     * the key to null.
     * @param key the key to be searched for.
     * @return the value Object specified by the key if it exist, otherwise null.
     */
    @Override
    public Object get(Object key){
        Set<String> s;
        s = index.get((String) key);
        return s;
    }
    
    /**
     * Returns an iterator over the elements in this <code>InvertedIndex</code>. 
     * The elements are returned in no particular order (unless this set is an 
     * instance of some class that provides a guarantee). 
     * @return an iterator over the elements in this <code>InvertedIndex</code>.
     */
    @Override
    public Iterator getIterator(){
        return index.keySet().iterator();
    }

    @SuppressWarnings( "unchecked" )
    @Override
    public Set<String> getCandidateList(ClusterRecord clusterRecord, Map<Integer, ArrayList<String>> lcrd, boolean mergedList) {
        Set<String> candidates = new HashSet<String>();
        OysterIdentityRecord oysterIdentityRecord = clusterRecord.getMergedRecord();
        Map<String, Integer> sort = new LinkedHashMap<String, Integer>();

        Set<String> hashes = getHash(oysterIdentityRecord);

        for (Iterator<String> it = hashes.iterator(); it.hasNext();) {
            String hash = it.next();
            Set<String> s = index.get(hash);
            
            if (s != null) {
                Set<String> temp = new HashSet<String>();
                for (Iterator<String> it2 = s.iterator(); it2.hasNext();){
                    String key = it2.next();
                        
                    int value = 0;
                    if (sort.containsKey(key)) {
                        value = sort.get(key);
                    }
                    value++;
                    sort.put(key, value);
                }
                candidates.addAll(temp);
            }
        }

        int value = 0;
        if (candidateList.containsKey(candidates.size())) {
            value = candidateList.get(candidates.size());
        }
        value++;
        candidateList.put(candidates.size(), value);
        
        // if more than 100 candidates only return the top 1/3 sorted based on most occuring
        if (candidates.size() > 100){
            TreeMap<Integer, Set<String>> sort2 = new TreeMap<Integer, Set<String>>();
            
            for(Iterator<Entry<String, Integer>> it = sort.entrySet().iterator(); it.hasNext();){
                Entry<String, Integer> entry = it.next();
                value = entry.getValue();
                
                Set<String> s2 = sort2.get(value);
                
                if (s2 == null) {
                    s2 = new LinkedHashSet<String>();
                }
                
                s2.add(entry.getKey());
                sort2.put(value, s2);
            }
            
            int check = candidates.size() / 3;
            if (check > 100) {
                check = 100;
            }
            
            candidates.clear();
            
            for (int i = sort2.lastKey(); i >= 0; i--){
                Set<String> s2 = sort2.get(i);
                
                if (s2 != null) {
                    candidates.addAll(s2);
                }
                
                if (candidates.size() > check) {
                    break;
                }
            }
        }

        return candidates;
    }

    private Set<String> getHash(OysterIdentityRecord oir) {
        Set<String> hashes = new LinkedHashSet<String>();

        for (Iterator<String> it = oir.getMetaData().keySet().iterator(); it.hasNext();) {
            String tag = it.next();
            String attributeName = oir.getMetaData().get(tag);

            if (!attributeName.equals("@OysterID") &&
                    !attributeName.equals("@RefID") &&
                    !attributeName.equals("@Assert")) {
                if (!passThruAttributes.contains(attributeName)) {
                    String token = oir.get(attributeName);

                    if (token != null) {
                        token = token.trim();

                        String [] temp = token.split("[|]");
                        for (int i = 0; i < temp.length; i++) {
                            if (temp[i] != null) {
                                hashes.add(temp[i]);
                            }
                        }
                    }
                }
            }
        }
        return hashes;
    }

    @Override
    public String indexStats() {
        StringBuilder sb = new StringBuilder(1000);
        
        // Send all output to the Appendable object sb
        Formatter report = new Formatter(sb, Locale.US);
        
        long totalTokens = 0L, maxTokens = 0L, minTokens = 0x7fffffffL, minTokensGT1 = 0x7fffffffL;
        Set<String> uniqueTokens = new HashSet<String>();
        TreeMap<Integer, Set<String>> topTenMaxKeys = new TreeMap<Integer, Set<String>>();
        TreeMap<Integer, Integer> tm = new TreeMap<Integer, Integer>();

        for (Iterator<String> it = index.keySet().iterator(); it.hasNext();){
            String key = it.next();
            Set<String> s = index.get(key);
            
            totalTokens += s.size();
            uniqueTokens.addAll(s);
            
            maxTokens = Math.max(maxTokens, s.size());
            minTokens = Math.min(minTokens, s.size());
            if (s.size() > 1) {
                minTokensGT1 = Math.min(minTokensGT1, s.size());
            }
            
            Set<String> keys = topTenMaxKeys.get(s.size());
            if (keys == null) {
                keys = new LinkedHashSet<String>();
            }
            keys.add(key);
            topTenMaxKeys.put(s.size(), keys);
            
            while (topTenMaxKeys.size() > 10){
                topTenMaxKeys.remove(topTenMaxKeys.firstKey());
            }
            
            int value = 0;
            if (tm.containsKey(s.size())) {
                value = tm.get(s.size());
            }
            value++;
            tm.put(s.size(), value);
        }
        
        report.format("Keys                    : %1$,12d%n", index.size());
        report.format("Total tokens            : %1$,12d%n", totalTokens);
        report.format("Unique tokens           : %1$,12d%n", uniqueTokens.size());
        report.format("Max tokens per key      : %1$,12d%n", maxTokens);
        report.format("Min tokens per key      : %1$,12d%n", minTokens);
        report.format("Min tokens > 1 per key  : %1$,12d%n", minTokensGT1);
        report.format(System.getProperty("line.separator"));
        
        report.format("Total tokens per key    : %1$,12.5f%n", (double)totalTokens/(double)index.size());
        report.format("Unique tokens per key   : %1$,12.5f%n", (double)uniqueTokens.size()/(double)index.size());
        report.format("Total per Unique tokens : %1$,12.5f%n", (double)totalTokens/(double)uniqueTokens.size());
        report.format("Unique per Total tokens : %1$,12.5f%n", (double)uniqueTokens.size()/(double)totalTokens);
        sb.append(System.getProperty("line.separator"));
        
        // calculate the Skew measures
        double xBar = (double)totalTokens/(double)index.size();
        double f, xf, m, m2 = 0, m3 = 0, m4 = 0;
        for (Iterator<Entry<Integer, Integer>> it = tm.entrySet().iterator(); it.hasNext();) {
            Entry<Integer, Integer> entry = it.next();

            f = entry.getValue();
            xf = entry.getKey() * entry.getValue();
            m = xf - xBar; // (xf−x̅)
            m2 += f * Math.pow(m, 2); // (xf−x̅)²f
            m3 += f * Math.pow(m, 3); // (xf−x̅)³f
            m4 += f * Math.pow(m, 4); // (xf−x̅)4f
        }
        
        m2 = m2 /(double)index.size();
        m3 = m3 /(double)index.size();
        m4 = m4 /(double)index.size();
        
        double skew = m3 / Math.pow(m2, 3D/2D); // m3 / m2^³/²
        double kurtosis = m4 / Math.pow(m2, 2); // m4 / m2²
        double excess = kurtosis - 3; // kurtosis−3
        
        report.format("Skewness                : %1$,12.5f%n", skew);
        report.format("Kurtosis                : %1$,12.5f%n", kurtosis);
        report.format("Excess                  : %1$,12.5f%n", excess);
        
        sb.append(System.getProperty("line.separator"));
        
        sb.append("Max key                 : ");
        Set<String> keys = topTenMaxKeys.get(topTenMaxKeys.lastKey());
        for (Iterator<String> it = keys.iterator(); it.hasNext();) {
            String key = it.next();
            sb.append(key);

            if (it.hasNext()) {
                sb.append(", ");
            }
        }
        sb.append(System.getProperty("line.separator"));
        sb.append(System.getProperty("line.separator"));
        
        sb.append("Top 10 keys             : ").append(System.getProperty("line.separator"));
        for (Iterator<Entry<Integer, Set<String>>> it = topTenMaxKeys.descendingMap().entrySet().iterator(); it.hasNext();){
            Entry<Integer, Set<String>> entry = it.next();
            keys = entry.getValue();
            
            sb.append(entry.getKey());
            if (keys != null){
                int count = 0;
                sb.append("                        : ");
                for (Iterator<String> it2 = keys.iterator(); it2.hasNext();){
                    String key = it2.next();
                    sb.append(key);
                    
                    if (it2.hasNext()) {
                        sb.append(", ");
                    }
                    
                    if (count == 10) {
                        sb.append("[").append(keys.size()-10).append(" More]...");
                        break;
                    }
                    count++;
                }
                sb.append(System.getProperty("line.separator"));
            }
        }
        
        sb.append(System.getProperty("line.separator"));
        sb.append(System.getProperty("line.separator"));
        sb.append("Candidate Size     # of Candidates        # of Records").append(System.getProperty("line.separator"));
        for (Iterator<Entry<Integer, Integer>> it = candidateList.entrySet().iterator(); it.hasNext();) {
            Entry<Integer, Integer> entry = it.next();
            report.format("  %1$,12d       %2$,13d     %3$,15d%n", entry.getKey(), entry.getValue(), entry.getKey() * entry.getValue());
        }
        
        sb.append(System.getProperty("line.separator"));
        sb.append(System.getProperty("line.separator"));
        sb.append("   Index Group          Index Size        # of Records").append(System.getProperty("line.separator"));
        for (Iterator<Entry<Integer, Integer>> it = tm.entrySet().iterator(); it.hasNext();) {
            Entry<Integer, Integer> entry = it.next();
            report.format("  %1$,12d       %2$,13d     %3$,15d%n", entry.getKey(), entry.getValue(), entry.getKey() * entry.getValue());
        }
        return sb.toString();
    }
}

