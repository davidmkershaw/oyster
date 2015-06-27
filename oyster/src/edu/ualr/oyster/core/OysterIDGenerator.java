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

import edu.ualr.oyster.ErrorFormatter;
import edu.ualr.oyster.data.OysterIdentityRecord;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Iterator;
import java.util.Locale;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * OysterIDGenerator.java
 * Created on Aug 20, 2010
 * @author Eric D. Nelson
 */
public class OysterIDGenerator {
    /** The message digest that will be used to produce the hash */
    private MessageDigest md = null;
    
    /**
     * Creates a new instance of OysterIDGenerator
     * Algorithm the name of the algorithm requested.
     * <ul>
     * <li>MD2: The MD2 message digest algorithm as defined in RFC 1319.</li>
     * <li>MD5: The MD5 message digest algorithm as defined in RFC 1321.</li>
     * <li>SHA-1: The Secure Hash Algorithm, as defined in Secure Hash Standard,
     * NIST FIPS 180-1.</li>
     * <li>SHA-256: SHA-256 is a 256-bit hash function intended to provide 128 
     * bits of security against collision attacks.</li>
     * <li>SHA-384: SHA-384-bit hash may be obtained by truncating the SHA-512 
     * output.</li>
     * <li>SHA-512: SHA-512 is a 512-bit hash function intended to provide 256 
     * bits of security.</li>
     * </ul>
     * @param algorithm the algorithm to use to create the hashed id.
     */
    public OysterIDGenerator(String algorithm){
        try {
            md = MessageDigest.getInstance(algorithm);
        } catch (NoSuchAlgorithmException ex) {
            Logger.getLogger(OysterIDGenerator.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }

    /**
     * Returns the OysterID for the input <code>OysterIdentityRecord</code>.
     * @param oir the <code>OysterIdentityRecord</code> used to create the id.
     * @param derived
     * @return the OysterID.
     */
    public String getOysterID(OysterIdentityRecord oir, boolean derived, Set<String> passThruAttributes){
        StringBuilder result = new StringBuilder();
        result.append("ZZZZZZZZZZZZZZZZ");
        StringBuilder mod = new StringBuilder();
        StringBuilder decimal = new StringBuilder();
        StringBuilder hex = new StringBuilder();
        String [] alphabet = {"0","1","2","3","4","5","6","7","8","9","A","B",
                              "C","D","E","F","G","H","I","J","K","L","M","N",
                              "O","P","Q","R","S","T","U","V","W","X","Y","Z"};
        // convert
        String [] hash;
        
        if (oir != null){
            try {
            OysterIdentityRecord temp = oir.clone();
//            temp.remove("@RefID");
            temp.remove("@OysterID");
            
            if (derived) {
                updateMD5("DERIVED: ");
            }
            
            for (Iterator<String> it = temp.getMetaData().keySet().iterator(); it.hasNext();){
                String tag = it.next();
                String attribute = temp.getMetaData().get(tag);
                if (!passThruAttributes.contains(attribute)){
                    String token = temp.get(attribute);

                    updateMD5(token);
                }
            }
                
            hash = convertMD5(false).split("[\\.]");
            
                result = new StringBuilder();
            for (int i = 0; i < hash.length; i++){
                    result.append(alphabet[Integer.parseInt(hash[i])%36]);
                    mod.append(Integer.parseInt(hash[i])%36).append(" ");
                    decimal.append(hash[i]).append(".");
                    hex.append(Integer.toHexString(Integer.parseInt(hash[i]))).append(" ");
            }
            /*
            System.out.println(ci.toString().toUpperCase());
            System.out.println("\t" + hex);
            System.out.println("\t" + decimal);
            System.out.println(" \t" + mod);
            System.out.println(" \t" + result);
            System.out.println();
            */
            } catch (CloneNotSupportedException ex) {
                Logger.getLogger(OysterIDGenerator.class.getName()).log(Level.SEVERE, null, ex);
            }
        } else {
            System.err.println("##ERROR: Null OIR sent to ID Generator.");
        }
        return result.toString();
    }

    /**
     * This method updates the message digest.
     * @param token the input String.
     */
    private void updateMD5(String token){
        if (token != null && !token.equals("")) {
            byte[] input = token.toUpperCase(Locale.US).trim().getBytes();
            md.update(input);
        }
    }

    /**
     * This method converts the message digest into a string.
     * @param hex true if the output hash is to be a hexadecimal, otherwise dotted decimal String.
     * @return a security hashed String
     */
    private String convertMD5(boolean hex) {
        StringBuilder result = new StringBuilder();
        byte[] output = md.digest();

        if (hex) {
            // convert to hex
            for (int i = 0; i < output.length; i++) {
                String s = Integer.toHexString((int) output[i] & 0xFF);
                if (s.length() == 1) {
                    s = "0" + s;
                }
                result.append(s);
            }
        } else {
            // convert to dotted decimal
            for (int i = 0; i < output.length; i++) {
                String num = "" + ((int) output[i] & 0xFF);
                if (num.length() == 1) {
                    num = "00" + num;
                } else if (num.length() == 2) {
                    num = "0" + num;
                }
                result.append(num).append(".");
            }
            // remove the final decimal point
            result = result.delete(result.length()-1, result.length());
        }
        return result.toString().trim();
    }
}
