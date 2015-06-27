/*
 * Copyright 2013 John Talburt, Eric Nelson
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

import java.util.Arrays;
import java.util.Locale;

/**
 * Scan.java
 * Created on Jun 9, 2012 12:12:49 AM
 * @author Eric D. Nelson
 */
public class Scan {
    /**
     * Creates a new instance of Scan
     */
    public Scan(){
    }
    
    public String getScan(String token, String direction, String charType, int length, String upperCase, String order){
        String result = null;
        
        if (token != null && !token.isEmpty()) {
            // LR, RL
            if (direction.equalsIgnoreCase("LR")) {
                result = token;
            } else {
                StringBuilder sb = new StringBuilder(token);
                sb.reverse();
                result = sb.toString();
            }

            // ALL, NONBLANK, ALPHA, LETTER and DIGIT
            if (charType.equalsIgnoreCase("ALL")) ;
            else if (charType.equalsIgnoreCase("NONBLANK")) {
                result = result.replaceAll("\\s", "").trim();
            } else if (charType.equalsIgnoreCase("ALPHA")) {
                result = result.replaceAll("\\W", "").trim();
            } else if (charType.equalsIgnoreCase("LETTER")) {
                result = result.replaceAll("[^a-zA-Z]", "").trim();
            } else if (charType.equalsIgnoreCase("DIGIT")) {
                result = result.replaceAll("\\D", "").trim();
            }

            // Get the correct length
            if (length != 0 && result.length() > length){
                result = result.substring(0, length);
            }
        
            // ToUpper, KeepCase
            if (upperCase.equalsIgnoreCase("ToUpper")) {
                result = result.toUpperCase(Locale.US);
            }
        
            // Same, L2HKeepDup and L2HDropDup
            if (order.equalsIgnoreCase("SameOrder")) {
                // if reversed changed back to normal
                if (direction.equalsIgnoreCase("RL")){
                    StringBuilder sb = new StringBuilder(result);
                    sb.reverse();
                    result = sb.toString();
                }
            } else if (order.equalsIgnoreCase("L2HKeepDup")) {
                result = order(result, false);
            } else if (order.equalsIgnoreCase("L2HDropDup")) {
                result = order(result, true);
            }

            // pad
            if (length != 0 && result.length() < length){
                if (direction.equalsIgnoreCase("LR")) {
                    result = padRight(result, length);
                } else {
                    result = padLeft(result, length);
                }
            }
        }
        return result;
    }
    
    public boolean compareScan(String s, String t, String direction, String charType, int length, String upperCase, String order) {
        String sScan = getScan(s, direction, charType, length, upperCase, order);
        String tScan = getScan(t, direction, charType, length, upperCase, order);
        
        boolean flag = false;
        if (sScan != null && tScan != null) {
            flag = sScan.equals(tScan);
        }
        
        return flag;
    }
    
    private String order(String s, boolean drop){
        StringBuilder sb = new StringBuilder(100);
        char [] a = s.toCharArray();
        Arrays.sort(a);
        
        if (a.length > 0) {
            sb.append(a[0]);
            char check = a[0];
            for (int i = 1; i < a.length; i++){
                if (drop){
                    if (check != a[i]) {
                        sb.append(a[i]);
                    }
                } else {
                    sb.append(a[i]);
                }

                check = a[i];
            }
        }
        
        return sb.toString();
    }

    private String padLeft(String s, int length) {
        String result = s;
        while (result.length() < length){
            result = "*" + result;
        }
        return result;
    }

    private String padRight(String s, int length) {
        StringBuilder result = new StringBuilder(length);
        result.append(s);
        while (result.length() < length){
            result.append("*");
        }
        return result.toString();
    }

    /**
     * @param args the command line arguments
     */
/*
    public static void main(String[] args) {
        Scan s = new Scan();
        // Scan(LR, ALPHA, 8, ToUpper, SameOrder)
        System.out.format("%1$s   %2$s%n", s.getScan("123 N. Oak St, Apt #5", "LR", "ALPHA", 8, "ToUpper", "SameOrder"), "123NOAKS");
        // Scan(RL, ALPHA, 8, ToUpper, SameOrder)
        System.out.format("%1$s   %2$s%n", s.getScan("123 N. Oak St, Apt #5", "RL", "ALPHA", 8, "ToUpper", "SameOrder"), "AKSTAPT5");
        // Scan(LR, DIGIT, 6, KeepCase, SameOrder)
        System.out.format("%1$s   %2$s%n", s.getScan("123 N. Oak St, Apt #5", "LR", "DIGIT", 6, "KeepCase", "SameOrder"), "1235**");
        // Scan(RL, DIGIT, 6, KeepCase, SameOrder)
        System.out.format("%1$s   %2$s%n", s.getScan("123 N. Oak St, Apt #5", "RL", "DIGIT", 6, "KeepCase", "SameOrder"), "**1235");
        // Scan(LR, NONBLANK, 20, KeepCase, SameOrder)
        System.out.format("%1$s   %2$s%n", s.getScan("123 N. Oak St, Apt #5", "LR", "NONBLANK", 20, "KeepCase", "SameOrder"), "123N.OakSt,Apt#5****");
        // Scan(LR, ALL, 10, ToUpper, SameOrder)
        System.out.format("%1$s   %2$s%n", s.getScan("123 N. Oak St, Apt #5", "LR", "ALL", 10, "ToUpper", "SameOrder"), "123 N. OAK");
        // Scan(LR, DIGIT, 9, KeepCase, SameOrder)
        System.out.format("%1$s   %2$s%n", s.getScan("412-67-1784", "LR", "DIGIT", 9, "KeepCase", "SameOrder"), "412671784");
        // Scan(LR, DIGIT, 9, KeepCase, L2HKeepDup)
        System.out.format("%1$s   %2$s%n", s.getScan("412-67-1784", "LR", "DIGIT", 9, "KeepCase", "L2HKeepDup"), "112446778");
        // Scan(LR, DIGIT, 9, KeepCase, L2HDropDup)
        System.out.format("%1$s   %2$s%n", s.getScan("412-67-1784", "LR", "DIGIT", 9, "KeepCase", "L2HDropDup"), "124678***");
        // Scan(RL, DIGIT, 7, KeepCase, SameOrder)
        System.out.format("%1$s   %2$s%n", s.getScan("+501-555-1234", "RL", "DIGIT", 7, "KeepCase", "SameOrder"), "5551234");
        // Scan(RL, DIGIT, 7, KeepCase, L2HKeepDup)
        System.out.format("%1$s   %2$s%n", s.getScan("+501-555-1234", "RL", "DIGIT", 7, "KeepCase", "L2HKeepDup"), "1234555");
        // Scan(RL, DIGIT, 7, KeepCase, L2HDropDup)
        System.out.format("%1$s   %2$s%n", s.getScan("+501-555-1234", "RL", "DIGIT", 7, "KeepCase", "L2HDropDup"), "**12345");
    }
*/
}
