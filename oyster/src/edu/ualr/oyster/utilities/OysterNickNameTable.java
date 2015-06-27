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

package edu.ualr.oyster.utilities;

import edu.ualr.oyster.ErrorFormatter;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Locale;
import java.util.Map;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * This class is used to determine if a source and target are equivalent. If the
 * source and target can be found in the lookup table, i.e. Robert ≈ Bob. This 
 * can also be used for any synonym lookup not just names. This table is backed 
 * by a table held in the distributions data folder called alias.dat. There is 
 * also a constructor that can be used to point to a different data file. Any 
 * other data file must be of this format:
 * <ul>
 * <li>Two column tab delimited</li>
 * <li>Any comments must be preceded by !! </li>
 * </ul>
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.C4D7B66D-D500-28C1-7A09-6DF8995F661F]
// </editor-fold> 
public class OysterNickNameTable {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.38B435FA-4A07-AC7B-A35B-741DA17592BB]
    // </editor-fold> 
    /** The Nickname table */
    private Map <String, ArrayList<String>> nicknameTable;


    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.370BE1BF-B9ED-F91B-2930-E7C1CDEB85AD]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>OysterNickNameTable</code>
     */
    public OysterNickNameTable () {
        nicknameTable = new LinkedHashMap <String, ArrayList<String>>();
        load("data/alias.dat");
    }

    /**
     * Creates a new instance of <code>OysterNickNameTable</code>
     * @param filename the data file to be loaded
     */
    public OysterNickNameTable (String filename) {
        load(filename);
    }

    /**
     * Loads the data file into the nickname table
     * @param filename the file to be loaded
     */
    private void load(String filename){
        int count = 0;
        String read;
        String [] text;
        BufferedReader infile = null;
        
        try{
            File file = new File(filename);
//            System.out.println("Loading " + file.getName());
            infile = new BufferedReader(new FileReader(file));
            while((read = infile.readLine()) != null){
                if (!read.startsWith("!!")) {
                    text = read.split("[\t]");
                    
                    // load proper name as key and alias as value
                    ArrayList<String> al;
                    al = nicknameTable.get(text[0].toUpperCase(Locale.US));
                    if (al == null) {
                        al = new ArrayList<String>();
                    }
                    
                    if (!al.contains(text[1].toUpperCase(Locale.US))) {
                        al.add(text[1].toUpperCase(Locale.US));
                    }
                    
                    nicknameTable.put(text[0].toUpperCase(Locale.US), al);
                    
                    // now load the alias as the key and the proper name as tha value
                    al = nicknameTable.get(text[1].toUpperCase(Locale.US));
                    if (al == null) {
                        al = new ArrayList<String>();
                    }
                    
                    if (!al.contains(text[0].toUpperCase(Locale.US))) {
                        al.add(text[0].toUpperCase(Locale.US));
                    }
                    
                    nicknameTable.put(text[1].toUpperCase(Locale.US), al);
                    
                    count++;
                }
            }
            
//            System.out.println(count + " elements loaded.\n");
        } catch(IOException ex){
            Logger.getLogger(OysterNickNameTable.class.getName()).log(Level.WARNING, ErrorFormatter.format(ex), ex);
        } finally {
            try {
                if (infile != null) {
                    infile.close();
                }
            } catch (IOException ex) {
                Logger.getLogger(OysterNickNameTable.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
            }
        }
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.0C76356C-4678-E026-2018-88464B38F4ED]
    // </editor-fold> 
    /**
     * Returns the Nickname Table for this <code>OysterNickNameTable</code>
     * @return the Nickname Table
     */
    public Map <String, ArrayList<String>> getNicknameTable () {
        return nicknameTable;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.EF9C84C0-CB11-EA2A-BEF6-6CA8722E56C0]
    // </editor-fold> 
    /**
     * Sets the Nickname Table for this <code>OysterNickNameTable</code>
     * @param nicknameTable the nickname table to be set
     */
    public void setNicknameTable (Map <String, ArrayList<String>> nicknameTable) {
        this.nicknameTable = nicknameTable;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.8F436E85-7036-7B5A-2F70-4F7DEDCBE0D7]
    // </editor-fold> 
    /**
     * One string is an alias for the other string as defined for that attribute
     * type (William - Bill)
     * @param s source String
     * @param t target String
     * @return true if this is a known nickname pair, otherwise false
     */
    public boolean isNicknamePair (String s, String t) {
        boolean flag = false;
        if (s == null && t == null) {
            flag = false;
        } else if (s != null && t == null) {
            flag = false;
        } else if (s == null && t != null) {
            flag = false;
        } else if (s != null && t != null){
            ArrayList<String> sal = nicknameTable.get(s.toUpperCase(Locale.US));
            ArrayList<String> tal = nicknameTable.get(t.toUpperCase(Locale.US));
            if (sal != null && tal != null){
                if (sal.contains(t.toUpperCase(Locale.US)) || tal.contains(s.toUpperCase(Locale.US))){
                    flag = true;
                }
            }
        }
        return flag;
    }
}

