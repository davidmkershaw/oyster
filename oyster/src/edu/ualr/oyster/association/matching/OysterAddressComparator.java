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

package edu.ualr.oyster.association.matching;

import edu.ualr.oyster.ErrorFormatter;
import edu.ualr.oyster.utilities.OysterEditDistance;
import edu.ualr.oyster.utilities.OysterUtilityTranspose;
import edu.ualr.oyster.utilities.QGramTetrahedralRatio;
import edu.ualr.oyster.utilities.Soundex;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.Locale;
import java.util.Map;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * OysterAddressComparator.java
 * Created on Jul 7, 2011 10:22:52 AM
 * @author enelso
 */
public class OysterAddressComparator extends OysterComparator{
    static private Map<String, String> directionals = new LinkedHashMap<String, String>();
    static private Map<String, String> thoroughfares = new LinkedHashMap<String, String>();
    static private Map<String, String> unitDesignators = new LinkedHashMap<String, String>();
    
    /** Single Character Transpose Utility */
    private OysterUtilityTranspose transpose;
    
    /** Levenshtein Edit Distance */
    private OysterEditDistance editDist;
    
    /** */
    private QGramTetrahedralRatio qGram;
    
    /** Standard Soundex utility */
    private Soundex soundex;
    
    /**
     * Creates a new instance of OysterAddressComparator
     */
    public OysterAddressComparator(){
        super();
        
        matchCodes.add("SIMILAR");
        
        // NOT operator
        matchCodes.add("~SIMILAR");
        
        transpose = new OysterUtilityTranspose();
        editDist = new OysterEditDistance();
        qGram = new QGramTetrahedralRatio();
        soundex = new Soundex();
        
        load("data/Directional.dat", 0);
        load("data/Thoroughfare.dat", 1);
        load("data/Unit Designators.dat", 2);
    }
    
    @Override
    /**
     * Returns the match code for this <code>OysterCompareADEFirstName</code>.
     * @param s source String.
     * @param t target String.
     * @param matchType the type of match to preform.
     * @return the match code.
     */
    public String getMatchCode(String s, String t, String matchType) {
        String result;
        float qTRThreshold = 0.25f, ledThreshold = 0.8f, total = 0f;
        int count = 0;
        boolean not = false;
        
        // Check for NOT operator
        if (matchType.toUpperCase(Locale.US).startsWith("~")){
            matchType = matchType.substring(1);
            not = true;
        }
        
        USAddress sAddress = parse(s);
        USAddress tAddress = parse(t);

        if (sAddress.primaryNumber != null && tAddress.primaryNumber != null) {
            if (sAddress.primaryNumber.equalsIgnoreCase(tAddress.primaryNumber)) {
                total++;
            } else if (transpose.differByTranspose(sAddress.primaryNumber, tAddress.primaryNumber)) {
                total += .5;
            } else {
                total--;
            }
            count++;
        } else if (sAddress.primaryNumber == null && tAddress.primaryNumber != null) {
            total--;
            count++;
        } else if (sAddress.primaryNumber != null && tAddress.primaryNumber == null) {
            total--;
            count++;
        }

        if (sAddress.preDirectional != null && tAddress.preDirectional != null) {
            if (sAddress.preDirectional.equalsIgnoreCase(tAddress.preDirectional)) {
                total++;
            } else {
                total--;
            }
            count++;
        } else if (sAddress.preDirectional == null && tAddress.preDirectional != null) {
            total--;
            count++;
        } else if (sAddress.preDirectional != null && tAddress.preDirectional == null) {
            total--;
            count++;
        }

        if (sAddress.primaryName != null && tAddress.primaryName != null) {
            editDist.computeDistance(sAddress.primaryName, tAddress.primaryName);

            if (sAddress.primaryName.equalsIgnoreCase(tAddress.primaryName)) {
                total++;
            } else if (transpose.differByTranspose(sAddress.primaryName, tAddress.primaryName)) {
                total += .5;
            } else if (soundex.compareSoundex(sAddress.primaryName, tAddress.primaryName)) {
                total += .5;
            } else if (qGram.qTR(sAddress.primaryName, tAddress.primaryName) >= qTRThreshold) {
                total += .5;
            } else if (editDist.computeNormalizedScore() >= ledThreshold) {
                total += .5;
            } else {
                total--;
            }
            count++;
        } else if (sAddress.primaryName == null && tAddress.primaryName != null) {
            total--;
            count++;
        } else if (sAddress.primaryName != null && tAddress.primaryName == null) {
            total--;
            count++;
        }

        if (sAddress.suffix != null && tAddress.suffix != null) {
            if (sAddress.suffix.equalsIgnoreCase(tAddress.suffix)) {
                total++;
            } else {
                total--;
            }
            count++;
        } else if (sAddress.suffix == null && tAddress.suffix != null) {
            total--;
            count++;
        } else if (sAddress.suffix != null && tAddress.suffix == null) {
            total--;
            count++;
        }

        if (sAddress.postDirectional != null && tAddress.postDirectional != null) {
            if (sAddress.postDirectional.equalsIgnoreCase(tAddress.postDirectional)) {
                total++;
            } else {
                total--;
            }
            count++;
        } else if (sAddress.postDirectional == null && tAddress.postDirectional != null) {
            total--;
            count++;
        } else if (sAddress.postDirectional != null && tAddress.postDirectional == null) {
            total--;
            count++;
        }

        if (sAddress.secUnitDes != null && tAddress.secUnitDes != null) {
            if (sAddress.secUnitDes.equalsIgnoreCase(tAddress.secUnitDes)) {
                total++;
            } else {
                total--;
            }
            count++;
        } else if (sAddress.secUnitDes == null && tAddress.secUnitDes != null) {
            total--;
            count++;
        } else if (sAddress.secUnitDes != null && tAddress.secUnitDes == null) {
            total--;
            count++;
        }

        if (sAddress.secNumber != null && tAddress.secNumber != null) {
            if (sAddress.secNumber.equalsIgnoreCase(tAddress.secNumber)) {
                total++;
            } else if (transpose.differByTranspose(sAddress.secNumber, tAddress.secNumber)) {
                total += .5;
            } else {
                total--;
            }
            count++;
        } else if (sAddress.secNumber == null && tAddress.secNumber != null) {
            total--;
            count++;
        } else if (sAddress.secNumber != null && tAddress.secNumber == null) {
            total--;
            count++;
        }

        if (sAddress.city != null && tAddress.city != null) {
            editDist.computeDistance(sAddress.city, tAddress.city);

            if (sAddress.city.equalsIgnoreCase(tAddress.city)) {
                total++;
            } else if (transpose.differByTranspose(sAddress.city, tAddress.city)) {
                total += .5;
            } else if (soundex.compareSoundex(sAddress.city, tAddress.city)) {
                total += .5;
            } else if (qGram.qTR(sAddress.city, tAddress.city) >= qTRThreshold) {
                total += .5;
            } else if (editDist.computeNormalizedScore() >= ledThreshold) {
                total += .5;
            } else {
                total--;
            }
            count++;
        } else if (sAddress.city == null && tAddress.city != null) {
            total--;
            count++;
        } else if (sAddress.city != null && tAddress.city == null) {
            total--;
            count++;
        }

        if (sAddress.state != null && tAddress.state != null) {
            editDist.computeDistance(sAddress.state, tAddress.state);

            if (sAddress.state.equalsIgnoreCase(tAddress.state)) {
                total++;
            } else if (transpose.differByTranspose(sAddress.state, tAddress.state)) {
                total += .5;
            } else if (soundex.compareSoundex(sAddress.state, tAddress.state)) {
                total += .5;
            } else if (qGram.qTR(sAddress.state, tAddress.state) >= qTRThreshold) {
                total += .5;
            } else if (editDist.computeNormalizedScore() >= ledThreshold) {
                total += .5;
            } else {
                total--;
            }
            count++;
        } else if (sAddress.state == null && tAddress.state != null) {
            total--;
            count++;
        } else if (sAddress.state != null && tAddress.state == null) {
            total--;
            count++;
        }

        if (sAddress.zip != null && tAddress.zip != null) {
            if (sAddress.zip.equalsIgnoreCase(tAddress.zip)) {
                total++;
            } else if (transpose.differByTranspose(sAddress.zip, tAddress.zip)) {
                total += .5;
            } else {
                total--;
            }
            count++;
        } else if (sAddress.zip == null && tAddress.zip != null) {
            total--;
            count++;
        } else if (sAddress.zip != null && tAddress.zip == null) {
            total--;
            count++;
        }

        if (sAddress.zip4 != null && tAddress.zip4 != null) {
            if (sAddress.zip4.equalsIgnoreCase(tAddress.zip4)) {
                total++;
            } else if (transpose.differByTranspose(sAddress.zip4, tAddress.zip4)) {
                total += .5;
            } else {
                total--;
            }
            count++;
        } else if (sAddress.zip4 == null && tAddress.zip4 != null) {
            total--;
            count++;
        } else if (sAddress.zip4 != null && tAddress.zip4 == null) {
            total--;
            count++;
        }
        /*
         System.out.println(sAddress);
         System.out.println(tAddress);
         System.out.println("Partial: " + total/(float)count);
         System.out.println("Total  : " + total/11f);
         System.out.println();
         */
        //======================================================================
        //======================================================================
        if (!not) {
            if ((total / (float) count > .1)) {
                result = matchType;
            } else {
                result = "X";
            }
        } else {
            if (!(total / (float) count > .1)) {
                result = matchType;
            } else {
                result = "X";
            }
        }

        return result;
    }
    
    private USAddress parse(String addressLine) {
        USAddress address = new USAddress();
        String[] temp = addressLine.split("[ ]");

        // check to see if the secondary address is first
        if (isUnitDesignator(temp[0])) {
//            System.out.println(addressLine);
//            System.out.println(temp.length);
            if (temp.length > 1) {
                temp = reorderAddress(temp);
            }
        }

        for (int i = 0; i < temp.length; i++) {
            if (i == 0 && !temp[i].equalsIgnoreCase("PO") && !temp[i].equalsIgnoreCase("RR")
                    && !temp[i].equalsIgnoreCase("P") && !temp[i].equalsIgnoreCase("R")) {
                address.primaryNumber = temp[i];
            } else if (isDirectional(temp[i])) {
                String token = directionals.get(temp[i].toUpperCase(Locale.US));
                if (address.primaryName == null) {
                    if (token != null) {
                        address.preDirectional = token;
                    } else {
                        address.preDirectional = temp[i];
                    }
                } else {
                    if (token != null) {
                        address.postDirectional = token;
                    } else {
                        address.postDirectional = temp[i];
                    }
                }
            } else if (isSuffix(temp[i])) {
                String token = thoroughfares.get(temp[i].toUpperCase(Locale.US));
                if (token != null) {
                    address.suffix = token;
                } else {
                    address.suffix = temp[i];
                }
            } else if (isUnitDesignator(temp[i])) {
                String token = unitDesignators.get(temp[i].toUpperCase(Locale.US));
                if (token != null) {
                    address.secUnitDes = token;
                } else {
                    address.secUnitDes = temp[i];
                }
            } else {
                if (!temp[i].trim().equals("")) {
                    if (address.secUnitDes != null) {
                        if (address.secNumber == null) {
                            address.secNumber = temp[i];
                        } else {
                            address.secNumber += " " + temp[i];
                        }
                    } else {
                        if (address.primaryName == null) {
                            address.primaryName = temp[i];
                        } else {
                            address.primaryName += " " + temp[i];
                        }
                    }
                }
            }
        }
        return address;
    }
    
    private USAddress parse(String address1, String address2) {
        USAddress address = new USAddress();

        // check to see if the secondary address is first
        if (isUnitDesignator(address1.split("[ ]")[0])) {
            String s = address1;
            address1 = address2;
            address2 = s;
        }

        String[] temp = address1.split("[ ]");

        for (int i = 0; i < temp.length; i++) {
            if (i == 0 && !temp[i].equalsIgnoreCase("PO") && !temp[i].equalsIgnoreCase("RR")
                    && !temp[i].equalsIgnoreCase("P") && !temp[i].equalsIgnoreCase("R")) {
                address.primaryNumber = temp[i];
            } else if (isDirectional(temp[i])) {
                String token = directionals.get(temp[i].toUpperCase(Locale.US));
                if (address.primaryName == null) {
                    if (token != null) {
                        address.preDirectional = token;
                    } else {
                        address.preDirectional = temp[i];
                    }
                } else {
                    if (token != null) {
                        address.postDirectional = token;
                    } else {
                        address.postDirectional = temp[i];
                    }
                }
            } else if (isSuffix(temp[i])) {
                String token = thoroughfares.get(temp[i].toUpperCase(Locale.US));
                if (token != null) {
                    address.suffix = token;
                } else {
                    address.suffix = temp[i];
                }
            } else {
                if (!temp[i].trim().equals("")) {
                    if (address.primaryName == null) {
                        address.primaryName = temp[i];
                    } else {
                        address.primaryName += " " + temp[i];
                    }
                }
            }
        }

        temp = address2.split("[ ]");

        for (int i = 0; i < temp.length; i++) {
            if (isUnitDesignator(temp[i])) {
                String token = unitDesignators.get(temp[i].toUpperCase(Locale.US));
                if (token != null) {
                    address.secUnitDes = token;
                } else {
                    address.secUnitDes = temp[i];
                }
            } else {
                if (!temp[i].trim().equals("")) {
                    if (address.secNumber == null) {
                        address.secNumber = temp[i];
                    } else {
                        address.secNumber += " " + temp[i];
                    }
                }
            }
        }
        return address;
    }

    private String[] reorderAddress(String[] temp) {
        String[] result = new String[temp.length];

        for (int i = 0; i < temp.length; i++) {
            if (i < 2) {
                result[temp.length + i - 2] = temp[i];
            } else {
                result[i - 2] = temp[i];
            }
        }

        return result;
    }

    private boolean isDirectional(String s) {
        boolean flag = false;
        if (directionals.containsKey(s.toUpperCase(Locale.US))) {
            flag = true;
        } else if (directionals.containsValue(s.toUpperCase(Locale.US))) {
            flag = true;
        }
        return flag;
    }

    private boolean isSuffix(String s) {
        boolean flag = false;
        if (thoroughfares.containsKey(s.toUpperCase(Locale.US))) {
            flag = true;
        } else if (thoroughfares.containsValue(s.toUpperCase(Locale.US))) {
            flag = true;
        }
        return flag;
    }

    private boolean isUnitDesignator(String s) {
        boolean flag = false;
        if (unitDesignators.containsKey(s.toUpperCase(Locale.US))) {
            flag = true;
        } else if (unitDesignators.containsValue(s.toUpperCase(Locale.US))) {
            flag = true;
        }
        return flag;
    }

    static private void load(String filename, int mode) {
        int count = 0;
        String read;
        String[] text;
        BufferedReader infile = null;

        try {
            File file = new File(filename);
//            System.out.println("Loading " + file.getName());
            infile = new BufferedReader(new FileReader(file));
            while ((read = infile.readLine()) != null) {
                if (!read.startsWith("!!")) {
                    text = read.split("[\t]");

                    if (mode == 0) {
                        directionals.put(text[0], text[1]);
                    } else if (mode == 1) {
                        thoroughfares.put(text[0], text[1]);
                    } else if (mode == 2) {
                        unitDesignators.put(text[0], text[1]);
                    }
                    count++;
                }
            }
//            System.out.println(count + " elements loaded.\n");
        } catch (FileNotFoundException ex) {
            Logger.getLogger(OysterAddressComparator.class.getName()).log(Level.WARNING, ErrorFormatter.format(ex), ex);
        } catch (IOException ex) {
            Logger.getLogger(OysterAddressComparator.class.getName()).log(Level.WARNING, ErrorFormatter.format(ex), ex);
        } finally {
            try {
                infile.close();
            } catch (IOException ex) {
                Logger.getLogger(OysterAddressComparator.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
    }
    
    class USAddress{
        String primaryNumber = null;
        String preDirectional = null;
        String primaryName = null;
        String suffix = null;
        String postDirectional = null;
        String secUnitDes = null;
        String secNumber = null;
        String city = null;
        String state = null;
        String zip = null;
        String zip4 = null;
        
        @Override
        public String toString(){
            StringBuilder sb = new StringBuilder();
            sb.append(primaryNumber).append("\t");
            sb.append(preDirectional).append("\t");
            sb.append(primaryName).append("\t");
            sb.append(suffix).append("\t");
            sb.append(postDirectional).append("\t");
            sb.append(secUnitDes).append("\t");
            sb.append(secNumber).append("\t");
            sb.append(city).append("\t");
            sb.append(state).append("\t");
            sb.append(zip).append("\t");
            sb.append(zip4);
            return sb.toString();
        }
    }
}
