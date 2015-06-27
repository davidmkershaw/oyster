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

import java.util.Locale;

/**
 * IBMAlphaCode.java
 * Created on May 15, 2010
 * 
 * IBM Alpha Inquiry System Personal Name Encoding System algorithm produce a 14
 * digit phonetic key of the name. Based on "An Overview of the Issues Related 
 * to the use of Personal Identifiers", by Mark Armstrong
 * 
 * @author Eric D. Nelson
 */
public class IBMAlphaCode {
    /**
     * Creates a new instance of IBMAlphaCode
     */
    public IBMAlphaCode(){
    }
    
    // FIXME: The article shows Kant returning 02100000000000 and Knuth returning
    // 07210000000000 I cannot get those results. In fact I get the exact oppisite
    // could it be possible that the author reversed these by accident?
    /**
     * This method determines the IBM Alpha Code hash for the input String.
     * @param s The input string
     * @return a String containing the encoding
     */
    public String getIBMAlphaCode(String s){
        StringBuilder result = new StringBuilder(32);
        char c, c2;
        int i = 0;
        
        if (s != null && !s.isEmpty()){
            String temp = s.toUpperCase(Locale.US);
            
            if (temp.startsWith("A")) {
                result.append("1");
                i++;
            } else if (temp.startsWith("E")) {
                result.append("1");
                i++;
            } else if (temp.startsWith("GF")) {
                result.append("08");
                i = 2;
            } else if (temp.startsWith("GM")) {
                result.append("03");
                i = 2;
            } else if (temp.startsWith("GN")) {
                result.append("02");
                i = 2;
            } else if (temp.startsWith("H")) {
                result.append("2");
                i++;
            } else if (temp.startsWith("I")) {
                result.append("1");
                i++;
            } else if (temp.startsWith("J")) {
                result.append("3");
                i++;
            } else if (temp.startsWith("KN")) {
                result.append("02");
                i = 2;
            } else if (temp.startsWith("O")) {
                result.append("1");
                i++;
            } else if (temp.startsWith("PF")) {
                result.append("08");
                i = 2;
            } else if (temp.startsWith("PN")) {
                result.append("02");
                i = 2;
            } else if (temp.startsWith("PS")) {
                result.append("00");
                i = 2;
            } else if (temp.startsWith("U")) {
                result.append("1");
                i++;
            } else if (temp.startsWith("W") && !temp.startsWith("WR")) {
                result.append("04");
                i = 2;
            } else if (temp.startsWith("Y")) {
                result.append("5");
                i++;
            } else {
                result.append("0");
            }
            
            int pass = 1;
            for (; i < temp.length(); i++){
                c = temp.charAt(i);
                
                switch(c){
                    case 'Z':result.append("0"); break;
                    case 'C': if (i+1 < temp.length()){
                                  c2 = temp.charAt(i+1);
                                  switch (c2){
                                      case 'E':
                                      case 'I':
                                      case 'Y': result.append("0"); i++; break;
                                      case 'H': if (pass == 1) {
                                                    result.append("6");
                                                } else if (pass == 2){
                                                    result.append("70");
                                                } else {
                                                    result.append("0");
                                                }
                                                i++;
                                                break;
                                      case 'K': if (pass == 1) {
                                                    result.append("7");
                                                } else if (pass == 2){
                                                    result.append("7");
                                                } else {
                                                    result.append("6");
                                                }
                                                i++;
                                                break;
                                      case 'Z': if (pass == 1) {
                                                    result.append("70");
                                                } else if (pass == 2){
                                                    result.append("6");
                                                } else {
                                                    result.append("0");
                                                }
                                                i++;
                                                break;
                                      default:  if (pass == 1) {
                                                    result.append("7");
                                                } else if (pass == 2){
                                                    result.append("7");
                                                } else {
                                                    result.append("6");
                                                }
                                  }
                              } else {
                                  if (pass == 1) {
                                      result.append("7");
                                  } else if (pass == 2) {
                                      result.append("7");
                                  } else {
                                      result.append("6");
                                  }
                              }
                              break;
                    case 'T': if (i+1 < temp.length()){
                                  c2 = temp.charAt(i+1);
                                  switch (c2){
                                      case 'S':
                                      case 'Z': if (pass == 1) {
                                                    result.append("0");
                                                } else {
                                                    result.append("10");
                                                }
                                                i++;
                                                break;
                                      default: result.append("1");
                                  }
                              } else {
                                  result.append("1");
                              }
                              break;
                    case 'D': if (i+1 < temp.length()){
                                  c2 = temp.charAt(i+1);
                                  switch (c2){
                                      case 'G': result.append("7"); i++; break;
                                      case 'S':
                                      case 'Z': if (pass == 1) {
                                                    result.append("0");
                                                } else {
                                                    result.append("10");
                                                }
                                                i++;
                                                break;
                                      default: result.append("1");
                              }
                              } else {
                                  result.append("1");
                              }
                              break;
                    case 'N': result.append("2"); break;
                    case 'M': result.append("3"); break;
                    case 'R': result.append("4"); break;
                    case 'L': result.append("5"); break;
                    case 'J': result.append("6"); break;
                    case 'S': if (i+1 < temp.length()){
                                  c2 = temp.charAt(i+1);
                                  switch (c2){
                                      case 'H': result.append("6"); i++; break;
                                      case 'C': if (i+2 < temp.length() && temp.charAt(i+2) == 'H'){
                                                    result.append("6");
                                                    i += 2;
                                                }
                                                break;
                                      default: result.append("0");
                                  }
                              } else {
                                  result.append("0");
                              }
                              break;
                    case 'K': if (pass == 1) {
                                  result.append("7");
                              } else if (pass == 2) {
                                  result.append("7");
                              } else {
                                  result.append("6");
                              }
                              break;
                    case 'G':
                    case 'Q':
                    case 'X': result.append("7"); break;
                    case 'F':
                    case 'V': result.append("8"); break;
                    case 'P': if (i+1 < temp.length()){
                                  c2 = temp.charAt(i+1);
                                  switch (c2){
                                      case 'H': result.append("8"); i++; break;
                                      default: result.append("9");
                                  }
                              } else {
                                  result.append("9");
                              }
                              break;
                    case 'B': result.append("9"); break;
                    default: //System.err.println("Invalid char:" + c);
                }
                pass++;
            }
            
            // Create 14 digit code
            if (result.length() > 14){
                result = result.delete(14, result.length());
            } else if (result.length() < 14){
                for (i = result.length(); i < 14; i++){
                    result.append("0");
                }
            }
            
            return result.toString();
        } else {
            return null;
        }
    }
    
    /**
     * This method compares two String using the IBM Alpha Code encoding. If the 
     * Strings produce the same encoding then the Strings are considered a 
     * match and true is returned.
     * @param s input source String
     * @param t input target String
     * @return true if the source and target are considered a match, otherwise
     * false.
     */
    public boolean compareAlphaCodes(String s, String t){
        boolean match = false;
        String sAlphaCode = getIBMAlphaCode(s);
        String tAlphaCode = getIBMAlphaCode(t);
        
        if (sAlphaCode !=  null && tAlphaCode != null) {
            match = sAlphaCode.equals(tAlphaCode);
        }
        
        return match;
    }
}
