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
 * Daitch–Mokotoff Soundex also called the Jewish Soundex or Eastern European 
 * Soundex, was designed to allow greater accuracy in the matching of Slavic and 
 * Yiddish surnames which have similar pronunciation but different spellings.
 * @see <a href="http://en.wikipedia.org/wiki/Daitch%E2%80%93Mokotoff_Soundex" > The Soundex </a>
 * @author Eric D. Nelson
 * Created on May 16, 2010
 */
public class DaitchMokotoffSoundex {
    /**
     * Creates a new instance of DaitchMokotoffSoundex
     */
    public DaitchMokotoffSoundex(){
    }

    /**
     * This method determines the Daitch–Mokotoff Soundex hash for the input 
     * String. This method potentially returns two differently encodings this is
     * due to some names having multiple possible pronunciations.
     * @param s The input string
     * @return a String array of length 2 containing the Daitch–Mokotoff encoding
     */
    public String[] getDMSoundex(String s) {
        String[] result = new String[2];
        StringBuilder primary = new StringBuilder();
        StringBuilder secondary = new StringBuilder();
        char c;

        if (s != null && s.length() > 0) {
            String temp = s.toUpperCase(Locale.US);
            result[0] = result[1] = "";

            //  Standardize the string by removing anything not A-Z 
            temp = temp.replaceAll("[^\\w]", "");
            temp = temp.replaceAll("[\\d]", "");
            
            for (int i = 0; i < temp.length(); i++) {
                c = temp.charAt(i);
                switch (c) {
                    case 'A':
                        if (i + 2 <= temp.length() && (temp.substring(i, i + 2).equals("AI") ||
                            temp.substring(i, i + 2).equals("AJ") || temp.substring(i, i + 2).equals("AY"))) {
                            if (i == 0) {
                                primary.append("0");
                                secondary.append("0");
                                i++;
                            } else if (temp.length() > i + 2 && isVowel(temp.charAt(i + 2))) {
                                primary.append("1");
                                secondary.append("1");
                                i++;
                            } else; // N/C
                        } else if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("AU")) {
                            if (i == 0) {
                                primary.append("0");
                                secondary.append("0");
                                i++;
                            } else if (temp.length() > i + 2 && isVowel(temp.charAt(i + 2))) {
                                primary.append("7");
                                secondary.append("7");
                                i++;
                            } else; // N/C
                        } else {
                            if (i == 0) {
                                primary.append("0");
                                secondary.append("0");
                            } else; // N/C
                        }
                        break;
                    case 'B':
                        primary.append("7");
                        secondary.append("7");
                        break;
                    case 'C':
                        if (i + 3 <= temp.length() && temp.substring(i, i + 3).equals("CHS")) {
                            if (i == 0) {
                                primary.append("5");
                                secondary.append("5");
                                i += 2;
                            } else {
                                primary.append("54");
                                secondary.append("54");
                            }
                        } else if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("CH")) {
                            primary.append("4");
                            secondary.append("5");
                            i++;
                        } else if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("CK")) {
                            primary.append("45");
                            secondary.append("5");
                            i++;
                        } else if (i + 2 <= temp.length() &&
                            (temp.substring(i, i + 2).equals("CZ") || temp.substring(i, i + 2).equals("CS"))) {
                            primary.append("4");
                            secondary.append("4");
                            i++;
                        } else if (i + 3 <= temp.length() &&
                            (temp.substring(i, i + 3).equals("CSZ") || temp.substring(i, i + 3).equals("CZS"))) {
                            primary.append("4");
                            secondary.append("4");
                            i += 2;
                        } else {
                            primary.append("4");
                            secondary.append("5");
                        }
                        break;
                    case 'D':
                        if (i + 3 <= temp.length() &&
                            ((temp.substring(i, i + 3).equals("DRZ") || temp.substring(i, i + 3).equals("DRS")) ||
                            (temp.substring(i, i + 3).equals("DSH") || temp.substring(i, i + 3).equals("DSZ")) ||
                            (temp.substring(i, i + 3).equals("DZH") || temp.substring(i, i + 3).equals("DZS")))) {
                            primary.append("4");
                            secondary.append("4");
                            i += 2;
                        } else if (i + 2 <= temp.length() &&
                            (temp.substring(i, i + 2).equals("DS") || temp.substring(i, i + 2).equals("DZ"))) {
                            primary.append("4");
                            secondary.append("4");
                            i++;
                        } else if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("DT")) {
                            primary.append("3");
                            secondary.append("3");
                            i++;
                        } else {
                            primary.append("3");
                            secondary.append("3");
                        }
                        break;
                    case 'E':
                        if (i + 2 <= temp.length() && (temp.substring(i, i + 2).equals("EI") ||
                            temp.substring(i, i + 2).equals("EJ") || temp.substring(i, i + 2).equals("EY"))) {
                            if (i == 0) {
                                primary.append("0");
                                secondary.append("0");
                                i++;
                            } else if (temp.length() > i + 2 && isVowel(temp.charAt(i + 2))) {
                                primary.append("1");
                                secondary.append("1");
                            } else; // N/C
                        } else if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("EU")) {
                            if (i == 0) {
                                primary.append("1");
                                secondary.append("1");
                                i++;
                            } else if (temp.length() > i + 2 && isVowel(temp.charAt(i + 2))) {
                                primary.append("1");
                                secondary.append("1");
                                i++;
                            } else; // N/C
                        } else {
                            if (i == 0) {
                                primary.append("0");
                                secondary.append("0");
                            }
                        }
                        break;
                    case 'F':
                        if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("FB")) {
                            primary.append("7");
                            secondary.append("7");
                            i++;
                        } else {
                            primary.append("7");
                            secondary.append("7");
                            i++;
                        }
                        break;
                    case 'G':
                        primary.append("5");
                        secondary.append("5");
                        break;
                    case 'H':
                        if (i == 0 || (temp.length() > i + 1 && isVowel(temp.charAt(i + 1)))) {
                            primary.append("5");
                            secondary.append("5");
                        }
                        break;
                    case 'I':
                        if (i + 2 <= temp.length() &&
                            (temp.substring(i, i + 2).equals("IA") || temp.substring(i, i + 2).equals("IE") ||
                            temp.substring(i, i + 2).equals("IO") || temp.substring(i, i + 2).equals("IU"))) {
                            if (i == 0) {
                                primary.append("1");
                                secondary.append("1");
                                i++;
                            }
                        } else {
                            if (i == 0) {
                                primary.append("0");
                                secondary.append("0");
                            }
                        }
                        break;
                    case 'J':
                        primary.append("4");
                        secondary.append("1");
                        break;
                    case 'K':
                        if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("KS")) {
                            if (i == 0) {
                                primary.append("5");
                                secondary.append("5");
                                i++;
                            } else {
                                primary.append("54");
                                secondary.append("54");
                            }
                        } else if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("KH")) {
                            primary.append("5");
                            secondary.append("5");
                            i++;
                        } else {
                            primary.append("5");
                            secondary.append("5");
                        }
                        break;
                    case 'L':
                        primary.append("8");
                        secondary.append("8");
                        break;
                    case 'M':
                        if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("MN")) {
                            primary.append("66");
                            secondary.append("66");
                            i++;
                        } else {
                            primary.append("6");
                            secondary.append("6");
                        }
                        break;
                    case 'N':
                        if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("NM")) {
                            primary.append("66");
                            secondary.append("66");
                            i++;
                        } else {
                            primary.append("6");
                            secondary.append("6");
                        }
                        break;
                    case 'O':
                        if (i + 2 <= temp.length() && (temp.substring(i, i + 2).equals("OI") ||
                            temp.substring(i, i + 2).equals("OJ") || temp.substring(i, i + 2).equals("OY"))) {
                            if (i == 0) {
                                primary.append("0");
                                secondary.append("0");
                                i++;
                            } else if (temp.length() > i + 3 && isVowel(temp.charAt(i + 3))) {
                                primary.append("1");
                                secondary.append("1");
                            } else; // N/C
                        } else {
                            if (i == 0) {
                                primary.append("0");
                                secondary.append("0");
                            } else; // N/C
                        }
                        break;
                    case 'P':
                        if (i + 2 <= temp.length() &&
                            (temp.substring(i, i + 2).equals("PF") || temp.substring(i, i + 2).equals("PH"))) {
                            primary.append("7");
                            secondary.append("7");
                            i++;
                        } else {
                            primary.append("7");
                            secondary.append("7");
                        }
                        break;
                    case 'Q':
                        primary.append("5");
                        secondary.append("5");
                        break;
                    case 'R':
                        if (i + 3 <= temp.length() && temp.substring(i, i + 3).equals("RTZ")) {
                            primary.append("9");
                            secondary.append("9");
                            i += 2;
                        } else if (i + 2 <= temp.length() && (temp.substring(i, i + 2).equals("RZ") ||
                            temp.substring(i, i + 2).equals("RS") || temp.substring(i, i + 2).equals("ZH"))) {
                            primary.append("9");
                            secondary.append("9");
                            i++;
                        } else {
                            primary.append("9");
                            secondary.append("9");
                        }
                        break;
                    case 'S':
                        if (i + 7 <= temp.length() && temp.substring(i, i + 7).equals("SCHTSCH")) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i += 6;
                            } else {
                                primary.append("4");
                                secondary.append("4");
                                i += 6;
                            }
                        } else if (i + 6 <= temp.length() &&
                            (temp.substring(i, i + 6).equals("SCHTSH") || temp.substring(i, i + 6).equals("SCHTCH"))) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i += 5;
                            } else {
                                primary.append("4");
                                secondary.append("4");
                                i += 5;
                            }
                        } else if (i + 5 <= temp.length() &&
                            (temp.substring(i, i + 5).equals("SHTCH") || temp.substring(i, i + 5).equals("SHTSH"))) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i += 4;
                            } else {
                                primary.append("4");
                                secondary.append("4");
                                i += 4;
                            }
                        } else if (i + 4 <= temp.length() && temp.substring(i, i + 4).equals("SHCH")) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i += 3;
                            } else {
                                primary.append("4");
                                secondary.append("4");
                                i += 3;
                            }
                        } else if (i + 4 <= temp.length() &&
                            (temp.substring(i, i + 4).equals("SCHT") || temp.substring(i, i + 4).equals("SCHD"))) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i += 3;
                            } else {
                                primary.append("43");
                                secondary.append("43");
                                i += 3;
                            }
                        } else if (i + 3 <= temp.length() && temp.substring(i, i + 3).equals("SHT")) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i += 2;
                            } else {
                                primary.append("43");
                                secondary.append("43");
                                i += 2;
                            }
                        } else if (i + 3 <= temp.length() && temp.substring(i, i + 3).equals("SCH")) {
                            primary.append("4");
                            secondary.append("4");
                            i += 2;
                        } else if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("SH")) {
                            primary.append("4");
                            secondary.append("4");
                            i++;
                        } else if (i + 5 <= temp.length() && temp.substring(i, i + 5).equals("STSCH")) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i += 4;
                            } else {
                                primary.append("4");
                                secondary.append("4");
                                i += 4;
                            }
                        } else if (i + 4 <= temp.length() && (temp.substring(i, i + 4).equals("STCH") ||
                            temp.substring(i, i + 4).equals("STRZ") || temp.substring(i, i + 4).equals("STRS") ||
                            temp.substring(i, i + 4).equals("STSH") || temp.substring(i, i + 4).equals("SZCZ") ||
                            temp.substring(i, i + 4).equals("SZCS"))) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i += 3;
                            } else {
                                primary.append("4");
                                secondary.append("4");
                                i += 3;
                            }
                        } else if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("SC")) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i++;
                            } else {
                                primary.append("4");
                                secondary.append("4");
                                i++;
                            }
                        } else if (i + 2 <= temp.length() &&
                            (temp.substring(i, i + 2).equals("ST") || temp.substring(i, i + 2).equals("SD"))) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i++;
                            } else {
                                primary.append("43");
                                secondary.append("43");
                                i++;
                            }
                        } else if (i + 3 <= temp.length() && (temp.substring(i, i + 3).equals("SZT") ||
                            temp.substring(i, i + 3).equals("SHD") || temp.substring(i, i + 3).equals("SZD"))) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i += 2;
                            } else {
                                primary.append("43");
                                secondary.append("43");
                                i += 2;
                            }
                        } else if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("SZ")) {
                            primary.append("4");
                            secondary.append("4");
                            i++;
                        } else {
                            primary.append("4");
                            secondary.append("4");
                            i++;
                        }
                        break;
                    case 'T':
                        if (i + 5 <= temp.length() && temp.substring(i, i + 5).equals("TTSCH")) {
                            primary.append("4");
                            secondary.append("4");
                            i += 4;
                        } else if (i + 4 <= temp.length() && temp.substring(i, i + 4).equals("TTCH")) {
                            primary.append("4");
                            secondary.append("4");
                            i += 4;
                        } else if (i + 3 <= temp.length() && (temp.substring(i, i + 3).equals("TCH") ||
                            temp.substring(i, i + 2).equals("THS"))) {
                            primary.append("4");
                            secondary.append("4");
                            i += 2;
                        } else if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("TH")) {
                            primary.append("3");
                            secondary.append("3");
                            i++;
                        } else if (i + 3 <= temp.length() && (temp.substring(i, i + 3).equals("TRZ") ||
                            temp.substring(i, i + 3).equals("TRS") || temp.substring(i, i + 3).equals("TSH"))) {
                            primary.append("4");
                            secondary.append("4");
                            i += 2;
                        } else if (i + 4 <= temp.length() && temp.substring(i, i + 4).equals("TSCH")) {
                            primary.append("4");
                            secondary.append("4");
                            i += 3;
                        } else if (i + 4 <= temp.length() && temp.substring(i, i + 4).equals("TTSZ")) {
                            primary.append("4");
                            secondary.append("4");
                            i += 3;
                        } else if (i + 3 <= temp.length() && temp.substring(i, i + 3).equals("TTS")) {
                            primary.append("4");
                            secondary.append("4");
                            i += 2;
                        } else if (i + 2 <= temp.length() && (temp.substring(i, i + 2).equals("TC") ||
                            temp.substring(i, i + 2).equals("TS"))) {
                            primary.append("4");
                            secondary.append("4");
                            i++;
                        } else if (i + 3 <= temp.length() && (temp.substring(i, i + 3).equals("TTZ") ||
                            temp.substring(i, i + 3).equals("TZS") || temp.substring(i, i + 3).equals("TSZ"))) {
                            primary.append("4");
                            secondary.append("4");
                            i += 2;
                        } else if (i + 2 <= temp.length() && (temp.substring(i, i + 2).equals("TZ") ||
                            temp.substring(i, i + 1).equals("TS"))) {
                            primary.append("4");
                            secondary.append("4");
                            i++;
                        } else {
                            primary.append("3");
                            secondary.append("3");
                        }
                        break;
                    case 'U':
                        if (i + 2 <= temp.length() && (temp.substring(i, i + 2).equals("UI") ||
                            temp.substring(i, i + 2).equals("UJ") || temp.substring(i, i + 2).equals("UY"))) {
                            if (i == 0) {
                                primary.append("0");
                                secondary.append("0");
                                i++;
                            } else if (temp.length() > i + 2 && isVowel(temp.charAt(i + 2))) {
                                primary.append("1");
                                secondary.append("1");
                            } else; // N/C
                        } else if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("UE")) {
                            if (i == 0) {
                                primary.append("0");
                                secondary.append("0");
                                i++;
                            }
                        } else {
                            if (i == 0) {
                                primary.append("0");
                                secondary.append("0");
                            }
                        }
                        break;
                    case 'V':
                        primary.append("7");
                        secondary.append("7");
                        break;
                    case 'W':
                        primary.append("7");
                        secondary.append("7");
                        break;
                    case 'X':
                        if (i == 0) {
                            primary.append("5");
                            secondary.append("5");
                        } else {
                            primary.append("54");
                            secondary.append("54");
                        }
                        break;
                    case 'Y':
                        if (i == 0) {
                            primary.append("1");
                            secondary.append("1");
                        }
                        break;
                    case 'Z':
                        if (i + 5 <= temp.length() && temp.substring(i, i + 5).equals("ZHDZH")) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i += 4;
                            } else {
                                primary.append("4");
                                secondary.append("4");
                                i += 4;
                            }
                        } else if (i + 4 <= temp.length() && temp.substring(i, i + 4).equals("ZDZH")) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i += 3;
                            } else {
                                primary.append("4");
                                secondary.append("4");
                                i += 3;
                            }
                        } else if (i + 3 <= temp.length() && temp.substring(i, i + 3).equals("ZDZ")) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i += 2;
                            } else {
                                primary.append("4");
                                secondary.append("4");
                                i += 2;
                            }
                        } else if (i + 3 <= temp.length() && temp.substring(i, i + 3).equals("ZHD")) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i += 2;
                            } else {
                                primary.append("43");
                                secondary.append("43");
                                i += 2;
                            }
                        } else if (i + 2 <= temp.length() && temp.substring(i, i + 2).equals("ZD")) {
                            if (i == 0) {
                                primary.append("2");
                                secondary.append("2");
                                i++;
                            } else {
                                primary.append("43");
                                secondary.append("43");
                                i++;
                            }
                        } else if (i + 4 <= temp.length() && temp.substring(i, i + 4).equals("ZSCH")) {
                            primary.append("4");
                            secondary.append("4");
                        } else if (i + 3 <= temp.length() && temp.substring(i, i + 3).equals("ZSH")) {
                            primary.append("4");
                            secondary.append("4");
                            i += 2;
                        } else if (i + 2 <= temp.length() && (temp.substring(i, i + 2).equals("ZH")) ||
                            temp.substring(i, i + 1).equals("ZS")) {
                            primary.append("4");
                            secondary.append("4");
                            i++;
                        } else {
                            primary.append("4");
                            secondary.append("4");
                        }
                        break;
                    default: System.err.println("Invalid char:" + c);
                }
            }

            primary.append("000000");
            secondary.append("000000");
            
            // Create 6 digit code
            if (primary.length() > 6) {
                result[0] = primary.toString().substring(0, 6);
                    }
            else {
                result[0] = primary.toString();
                }
            
            if (secondary.length() > 6) {
                result[1] = secondary.toString().substring(0, 6);
            }
            else {
                result[1] = secondary.toString();
            }
        }

        return result;
    }

    /**
     * This method compares two String using the Daitch–Mokotoff Soundex. If
     * the Strings produce the same encoding then the Strings are considered a 
     * match and true is returned.
     * @param s input source String
     * @param t input target String
     * @return true if the source and target are considered a match, otherwise
     * false.
     */
    public boolean compareDMSoundex(String s, String t){
        boolean flag = false;
        
        String [] sSoundex = getDMSoundex(s);
        String [] tSoundex = getDMSoundex(t);
        
        for (int i = 0; i < sSoundex.length; i++){
            for (int j = 0; j < tSoundex.length; j++){
                if (sSoundex[i].equals(tSoundex[j]) && sSoundex[i] != null){
                    flag = true;
                    break;
                }
            }
        }
        
        return flag;
    }
    
    /**
     * Determines if the input character is a vowel.
     * @param c the character to check
     * @return <code>true</code> if this is vowel; <code>false</code> otherwise.
     */
    private boolean isVowel(char c){
        boolean flag;
        switch (c){
            case 'A':
            case 'E':
            case 'I':
            case 'O':
            case 'U': flag = true; break;
            default: flag = false;
        }
        return flag;
    }
}
