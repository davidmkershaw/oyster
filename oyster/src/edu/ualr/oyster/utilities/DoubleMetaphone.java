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
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * DoubleMetaphone.java
 *
 * http://en.wikipedia.org/wiki/Double_Metaphone
 * Created on Apr 29, 2012 8:38:38 AM
 * @author Eric D. Nelson
 */
public class DoubleMetaphone {
    /**
     * Creates a new instance of DoubleMetaphone
     */
    public DoubleMetaphone(){
    }

    public String [] getDoubleMetaphone(String s) {
        String[] result = new String[2];
        String temp = "";
        StringBuilder primary = new StringBuilder();
        StringBuilder secondary = new StringBuilder();
        boolean germanic = false;
        char c;

        try {
            if (s != null && s.trim().length() > 0) {
                temp = s.toUpperCase(Locale.US);
                result[0] = result[1] = "";

                // 1. Standardize the string by removing all punctuations and digits
                temp = temp.replaceAll("\\p{Punct}", "");
                temp = temp.replaceAll("[\\d]", "");

                int i = 0;
                if (temp.startsWith("GN") || temp.startsWith("KN") ||
                    temp.startsWith("PN") || temp.startsWith("WR") ||
                    temp.startsWith("PS")) {
                    i = 1;
                }

                // is the the string gemanic
                if (temp.indexOf('W') != -1 || temp.indexOf('K') != -1 ||
                    temp.indexOf("CZ") != -1 || temp.indexOf("WITZ") != -1) {
                    germanic = true;
                }

                while (i < temp.length()) {
                    c = temp.charAt(i);

                    switch (c) {
                        case 'A':
                        case 'E':
                        case 'I':
                        case 'O':
                        case 'U':
                        case 'Y': // all init vowels now map to 'A'
                            if (i == 0) {
                                primary.append('A');
                                secondary.append('A');
                            }
                            i++;
                            break;
                        case 'B': // '-mb', e.g. "dumb", already skipped over ...
                            primary.append('P');
                            secondary.append('P');
                            if (matches(temp, "B", i+1)){
                                i += 2;
                            } else {
                                i++;
                            }
                            break;
                        case 'Ç':
                            primary.append('S');
                            secondary.append('S');
                            i++;
                            break;
                        case 'C': // various gremanic
                            if (!isVowel(charAt(temp, i-2)) && matches(temp, "ACH", i-1) &&
                                 ((!matches(temp, "I", i+2) && !matches(temp, "E", i+2)) ||
                                    temp.contains("BACHER") || temp.contains("MACHER"))) {
                                primary.append('K');
                                secondary.append('K');
                                i += 2;
                                break;
                            }

                            // special case 'caesar'
                            if (i == 0 && matches(temp, "CAESAR", i)) {
                                primary.append('S');
                                secondary.append('S');
                                i += 2;
                                break;
                            }

                            // italian 'chianti'
                            if (matches(temp, "CHIA", i)) {
                                primary.append('K');
                                secondary.append('K');
                                i += 2;
                                break;
                            }

                            if (matches(temp, "CH", i)) {
                                // find 'michael'
                                if (i > 0 && matches(temp, "CHAE", i)) {
                                    primary.append('K');
                                    secondary.append('X');
                                    i += 2;
                                    break;
                                }

                                // greek roots e.g. 'chemistry', 'chorus'
                                if (i == 0 &&
                                    ((matches(temp, "HARAC", i+1) || matches(temp, "HARIS", i+1)) ||
                                     (matches(temp, "HOR", i+1) || matches(temp, "HYM", i+1) ||
                                      matches(temp, "HIA", i+1) || matches(temp, "HEM", i+1))) &&
                                    !matches(temp, "CHORE", 0)) {
                                    primary.append('K');
                                    secondary.append('K');
                                    i += 2;
                                    break;
                                }

                                // germanic, greek, or otherwise 'ch' for 'kh' sound
                                if ((matches(temp, "VAN ", 0) || matches(temp, "VON ", 0)
                                    || matches(temp, "SCH", 0))
                                    // 'architect' but not 'arch', orchestra', 'orchid'
                                    || matches(temp, "ORCHES", i-2)
                                    || matches(temp, "ARCHIT", i-2)
                                    || matches(temp, "ORCHID", i-2)
                                    || matches(temp, "T", i+2)
                                    || matches(temp, "S", i+2)
                                    || ((matches(temp, "A", i-1)
                                    ||  matches(temp, "O", i-1)
                                    ||  matches(temp, "U", i-1)
                                    ||  matches(temp, "E", i-1)
                                    ||  i == 0)
                                    // e.g. 'wachtler', 'weschsler', but not 'tichner'
                                    && (matches(temp, "L", i+2) || matches(temp, "R", i+2)
                                    ||  matches(temp, "N", i+2) || matches(temp, "M", i+2)
                                    ||  matches(temp, "B", i+2) || matches(temp, "H", i+2)
                                    ||  matches(temp, "F", i+2) || matches(temp, "V", i+2)
                                    ||  matches(temp, "W", i+2) || matches(temp, " ", i+2)))) {
                                    primary.append('K');
                                    secondary.append('K');
                                } else {
                                    if (i > 0) {
                                        if (matches(temp, "MC", 0)) {
                                            // e.g. 'McHugh'
                                            primary.append('K');
                                            secondary.append('K');
                                        } else {
                                            primary.append('X');
                                            secondary.append('K');
                                        }
                                    } else {
                                        primary.append('X');
                                        secondary.append('X');
                                    }
                                }
                                i += 2;
                                break;
                            }

                            // e.g. 'czerny'
                            if (matches(temp, "CZ", i)
                                && !matches(temp, "WICZ", i-2)) {
                                primary.append('S');
                                secondary.append('X');
                                i += 2;
                                break;
                            }

                            // e.g. 'focaccia'
                            if (matches(temp, "CIA", i+1)) {
                                primary.append('X');
                                secondary.append('X');
                                i += 3;
                                break;
                            }

                            // double 'C', but not McClellan'
                            if (matches(temp, "CC", i) && i != 1
                                && !matches(temp, "M", 0)) {
                                // 'bellocchio' but not 'bacchus'
                                if (matches(temp, "I", i+2) ||
                                    matches(temp, "E", i+2) ||
                                    matches(temp, "H", i+2)
                                    && !matches(temp, "HU", i+2)) {
                                    // 'accident', 'accede', 'succeed'
                                    if (((i == 1)
                                        && (matches(temp, "A", i-1))
                                        ||  matches(temp, "UCCEE", i-1)
                                        ||  matches(temp, "UCCES", i-1))) {
                                        primary.append("KS");
                                        secondary.append("KS");
                                        // 'bacci', 'bertucci', other italian
                                    } else {
                                        primary.append("X");
                                        secondary.append("X");
                                    }
                                    i += 3;
                                    break;
                                } else {
                                    // Pierce's rule
                                    primary.append("K");
                                    secondary.append("K");
                                    i += 2;
                                    break;
                                }
                            }

                            if (matches(temp, "CK", i) ||
                                matches(temp, "CG", i) ||
                                matches(temp, "CQ", i)) {
                                primary.append("K");
                                secondary.append("K");
                                i += 2;
                                break;
                            }

                            if (matches(temp, "CI", i) ||
                                matches(temp, "CE", i) ||
                                matches(temp, "CY", i)) {
                                // italian vs. english
                                if (matches(temp, "CIO", i) ||
                                    matches(temp, "CIE", i) ||
                                    matches(temp, "CIA", i)) {
                                    primary.append("S");
                                    secondary.append("X");
                                } else {
                                    primary.append("S");
                                    secondary.append("S");
                                }
                                i += 2;
                                break;
                            }

                            // else
                            primary.append("K");
                            secondary.append("K");

                            // name sent in 'mac caffrey', 'mac gregor'
                            if (matches(temp, " C", i+1) ||
                                matches(temp, " Q", i+1) ||
                                matches(temp, " G", i+1)) {
                                i += 3;
                            } else {
                                if ((matches(temp, "C", i+1) ||
                                     matches(temp, "K", i+1) ||
                                     matches(temp, "Q", i+1))
                                    && !matches(temp, "CE", i+1) &&
                                       !matches(temp, "CI", i+1)) {
                                    i += 2;
                                } else {
                                    i++;
                                }
                            }
                            break;

                        case 'D':
                            if (matches(temp, "DG", i)) {
                                if (matches(temp, "I", i+2) ||
                                    matches(temp, "E", i+2) ||
                                    matches(temp, "Y", i+2)) {
                                    // e.g. 'edge'
                                    primary.append("J");
                                    secondary.append("J");
                                    i += 3;
                                    break;
                                } else {
                                    // e.g. 'edgar'
                                    primary.append("TK");
                                    secondary.append("TK");
                                    i += 2;
                                    break;
                                }
                            }

                            if (matches(temp, "DT", i) ||
                                matches(temp, "DD", i)) {
                                primary.append("T");
                                secondary.append("T");
                                i += 2;
                                break;
                            }

                            // else
                            primary.append("T");
                            secondary.append("T");
                            i++;
                            break;

                        case 'F':
                            if (matches(temp, "F", i+1)) {
                                i += 2;
                            } else {
                                i++;
                            }
                            primary.append("F");
                            secondary.append("F");
                            break;

                        case 'G':
                            if (matches(temp, "H", i+1)) {
                                if (i > 0 && !isVowel(charAt(temp, i-1))) {
                                    primary.append("K");
                                    secondary.append("K");
                                    i += 2;
                                    break;
                                }

                                if (i < 3) {
                                    // 'ghislane', 'ghiradelli'
                                    if (i == 0) {
                                        if (matches(temp, "I", i+2)) {
                                            primary.append("J");
                                            secondary.append("J");
                                        } else {
                                            primary.append("K");
                                            secondary.append("K");
                                        }
                                        i += 2;
                                        break;
                                    }
                                }

                                // Parker's rule (with some further refinements) - e.g. 'hugh'
                                if (((i > 1) &&
                                     (matches(temp, "B", i-2) ||
                                      matches(temp, "H", i-2) ||
                                      matches(temp, "D", i-2)))
                                    // e.g. 'bough'
                                    || ((i > 2)
                                    &&  (matches(temp, "B", i-3) ||
                                         matches(temp, "H", i-3) ||
                                         matches(temp, "D", i-3)))
                                    // e.g. 'broughton'
                                    || ((i > 3)
                                    && (matches(temp, "B", i-4) ||
                                        matches(temp, "H", i-4)))) {
                                    i += 2;
                                    break;
                                } else {
                                    // e.g. 'laugh', 'McLaughlin', 'cough', 'gough', 'rough', 'tough'
                                    if (i > 2 && matches(temp, "U", i-1)
                                        && (matches(temp, "C", i-3) ||
                                            matches(temp, "G", i-3) ||
                                            matches(temp, "L", i-3) ||
                                            matches(temp, "R", i-3) ||
                                            matches(temp, "T", i-3))) {
                                        primary.append("F");
                                        secondary.append("F");
                                    } else if (i > 0 && !matches(temp, "I", i-1)) {
                                        primary.append("K");
                                        secondary.append("K");
                                    }
                                    i += 2;
                                    break;
                                }
                            }

                            if (matches(temp, "N", i+1)) {
                                if (i == 1 && isVowel(charAt(temp, 0)) && !germanic) {
                                    primary.append("KN");
                                    secondary.append("N");
                                } else {
                                    // not e.g. 'cagney'
                                    if (!matches(temp, "EY", i+2)
                                        && !matches(temp, "Y", i+1)
                                        && !germanic) {
                                        primary.append("N");
                                        secondary.append("KN");
                                    } else {
                                        primary.append("KN");
                                        secondary.append("KN");
                                    }
                                }
                                i += 2;
                                break;
                            }

                            // 'tagliaro'
                            if (matches(temp, "LI", i+1) && !germanic) {
                                primary.append("KL");
                                secondary.append("L");
                                i += 2;
                                break;
                            }

                            // -ges-, -gep-, -gel- at beginning
                            if (i == 0 &&
                               (matches(temp, "Y", i+1) ||
                               (matches(temp, "ES", i+1) ||
                                matches(temp, "EP", i+1) ||
                                matches(temp, "EB", i+1) ||
                                matches(temp, "EL", i+1) ||
                                matches(temp, "EY", i+1) ||
                                matches(temp, "IB", i+1) ||
                                matches(temp, "IL", i+1) ||
                                matches(temp, "IN", i+1) ||
                                matches(temp, "IE", i+1) ||
                                matches(temp, "EI", i+1) ||
                                matches(temp, "ER", i+1)))) {
                                primary.append("K");
                                secondary.append("J");
                                i += 2;
                                break;
                            }

                            // -ger-, -gy-
                            if (matches(temp, "ER", i+1) ||
                                matches(temp, "Y", i+1)
                                && (!matches(temp, "DANGER", 0) ||
                                    !matches(temp, "RANGER", 0) ||
                                    !matches(temp, "MANGER", 0))
                                && (!matches(temp, "E", i-1) ||
                                    !matches(temp, "I", i-1))
                                && (!matches(temp, "RGY", i-1) ||
                                    !matches(temp, "OGY", i-1))) {
                                primary.append("K");
                                secondary.append("J");
                                i += 2;
                                break;
                            }

                            // italian e.g. 'biaggi'
                            if ((matches(temp, "E", i+1) ||
                                 matches(temp, "I", i+1) ||
                                 matches(temp, "Y", i+1))
                                || (matches(temp, "AGGI", i-1) ||
                                    matches(temp, "OGGI", i-1))) {
                                // obvious germanic
                                if (matches(temp, "VAN ", 0) ||
                                    matches(temp, "VON ", 0) ||
                                    matches(temp, "SCH",  0) ||
                                    matches(temp, "ET", i+1)) {
                                    primary.append("K");
                                    secondary.append("K");
                                } else {
                                    // always soft if french ending
                                    if (matches(temp, "IER ", i+1)) {
                                        primary.append("J");
                                        secondary.append("J");
                                    } else {
                                        primary.append("J");
                                        secondary.append("K");
                                    }
                                }
                                i += 2;
                                break;
                            }

                            if (matches(temp, "G", i+1)) {
                                i += 2;
                            } else {
                                i++;
                            }
                            primary.append('K');
                            secondary.append('K');
                            break;

                        case 'H':
                            // only keep if first & before vowel or btw. 2 vowels
                            if ((i == 0 || isVowel(charAt(temp,i-1)))
                                && isVowel(charAt(temp, i+1))) {
                                primary.append('H');
                                secondary.append('H');
                                i += 2;
                            } else {
                                i++;
                            }
                            break;

                        case 'J':
                            // obvious spanish, 'jose', 'san jacinto'
                            if (matches(temp, "JOSE", i) || matches(temp, "SAN ", 0)) {
                                if ((i == 0 && matches(temp, " ", i+4) || matches(temp, "SAN ", 0))) {
                                    primary.append('H');
                                    secondary.append('H');
                                } else {
                                    primary.append("J");
                                    secondary.append('H');
                                }
                                i++;
                                break;
                            }

                            if (i == 0 && !matches(temp, "JOSE", i)) {
                                // Yankelovich/Jankelowicz
                                primary.append('J');
                                secondary.append('A');
                            } else {
                                // spanish pron. of .e.g. 'bajador'
                                if (isVowel(charAt(temp, i-1)) && !germanic
                                    && (matches(temp, "A", i+1)
                                    ||  matches(temp, "O", i+1))) {
                                    primary.append("J");
                                    secondary.append("H");
                                } else {
                                    if (i == temp.length()-1) {
                                        primary.append("J");
                                        secondary.append("");
                                    } else {
                                        if ((!matches(temp, "L", i+1) ||
                                             !matches(temp, "T", i+1) ||
                                             !matches(temp, "K", i+1) ||
                                             !matches(temp, "S", i+1) ||
                                             !matches(temp, "N", i+1) ||
                                             !matches(temp, "M", i+1) ||
                                             !matches(temp, "B", i+1) ||
                                             !matches(temp, "Z", i+1)) &&
                                            (!matches(temp, "S", i-1) ||
                                             !matches(temp, "K", i-1) ||
                                             !matches(temp, "L", i-1))) {
                                            primary.append("J");
                                            secondary.append("J");
                                        }
                                    }
                                }
                            }

                            // it could happen
                            if (matches(temp, "J", i+1)) { 
                                i += 2;
                            } else {
                                i++;
                            }
                            break;

                        case 'K':
                            if (matches(temp, "K", i+1)) {
                                i += 2;
                            } else {
                                i++;
                            }
                            primary.append("K");
                            secondary.append("K");
                            break;

                        case 'L':
                            if (matches(temp, "L", i+1)) {
                                // spanish e.g. 'cabrillo', 'gallegos'
                                if (((i == temp.length()-3)
                                    && (matches(temp, "ILLO", i-1) ||
                                        matches(temp, "ILLA", i-1) ||
                                        matches(temp, "ALLE", i-1))
                                    || (((matches(temp, "AS", temp.length()-2) ||
                                          matches(temp, "OS", temp.length()-2))
                                    || (matches(temp, "A", temp.length()-1) ||
                                        matches(temp, "O", temp.length()-1)))
                                    && (matches(temp, "ALLE", i-1))))) {
                                    primary.append("L");
                                    secondary.append("");
                                    i += 2;
                                    break;
                                }
                                i += 2;
                            } else {
                                i++;
                            }
                            primary.append("L");
                            secondary.append("L");
                            break;

                        case 'M':
                            if (matches(temp, "UMB", i-1) &&
                               ((i+1) == temp.length()-1 || matches(temp, "ER", i+2))){
                                i += 2;
                            } else {
                                i++;
                            }
                            primary.append("M");
                            secondary.append("M");
                            break;

                        case 'N':
                            if (matches(temp, "N", i+1)) {
                                i += 2;
                            } else {
                                i++;
                            }
                            primary.append("N");
                            secondary.append("N");
                            break;

                        case 'Ñ':
                            i++;
                            primary.append("N");
                            secondary.append("N");
                            break;

                        case 'P':
                            if (matches(temp, "H", i+1)) {
                                i += 2;
                                primary.append("F");
                                secondary.append("F");
                                break;
                            }

                            // also account for "campbell" and "raspberry"
                            if (matches(temp, "P", i+1) ||
                                matches(temp, "B", i+1)) {
                                i += 2;
                            } else {
                                i++;
                            }
                            primary.append("P");
                            secondary.append("P");
                            break;

                        case 'Q':
                            if (matches(temp, "Q", i+1)) {
                                i += 2;
                            } else {
                                i++;
                            }
                            primary.append("K");
                            secondary.append("K");
                            break;

                        case 'R':
                            // french e.g. 'rogier', but exclude 'hochmeier'
                            if ((i == temp.length()-1)
                                && !germanic
                                && (matches(temp, "IE", i-2))
                                && (!matches(temp, "ME", i-4) &&
                                    !matches(temp, "MA", i-4))) {
                                primary.append("");
                                secondary.append("R");
                            } else {
                                primary.append("R");
                                secondary.append("R");
                            }

                            if (matches(temp, "R", i+1)) {
                                i += 2;
                            } else {
                                i++;
                            }
                            break;

                        case 'S':
                            // special cases 'island', 'isle', 'carlisle', 'carlysle'
                            if (matches(temp, "ISL", i-1) ||
                                matches(temp, "YSL", i-1)) {
                                i++;
                                break;
                            }

                            // special case 'sugar-'
                            if (i == 0 && matches(temp, "SUGAR", i)) {
                                primary.append("X");
                                secondary.append("S");
                                i++;
                                break;
                            }

                            if (matches(temp, "SH", i)) {
                                // germanic
                                if (matches(temp, "HEIM", i+1) ||
                                    matches(temp, "HOEK", i+1) ||
                                    matches(temp, "HOLM", i+1) ||
                                    matches(temp, "HOLZ", i+1)) {
                                    primary.append("S");
                                    secondary.append("S");
                                } else {
                                    primary.append("X");
                                    secondary.append("X");
                                }
                                i += 2;
                                break;
                            }

                            // italian & armenian
                            if (matches(temp, "SIO", i) ||
                                matches(temp, "SIA", i) ||
                                matches(temp, "SIAN", i)) {
                                if (germanic) {
                                    primary.append("S");
                                    secondary.append("S");
                                } else {
                                    primary.append("S");
                                    secondary.append("X");
                                }
                                i += 3;
                                break;
                            }

                            // german & anglicisations, e.g. 'smith' match 'schmidt', 'snider' match 'schneider'
                            // also, -sz- in slavic language altho in hungarian it is pronounced 's'
                            if (((i == 0) &&
                                    (matches(temp, "M", i+1) ||
                                     matches(temp, "N", i+1) ||
                                     matches(temp, "L", i+1) ||
                                     matches(temp, "W", i+1)))
                                || matches(temp, "Z", i+1)) {
                                primary.append("S");
                                secondary.append("X");
                                if (matches(temp, "Z", i+1)) {
                                    i += 2;
                                } else {
                                    i++;
                                }
                                break;
                            }

                            if (matches(temp, "SC", i)) {
                                // Schlesinger's rule
                                if (matches(temp, "H", i+2)) {
                                    // dutch origin, e.g. 'school', 'schooner'
                                    if (matches(temp, "OO", i+3) ||
                                        matches(temp, "ER", i+3) ||
                                        matches(temp, "EN", i+3) ||
                                        matches(temp, "UY", i+3) ||
                                        matches(temp, "ED", i+3) ||
                                        matches(temp, "EM", i+3)) {
                                        // 'schermerhorn', 'schenker'
                                        if (matches(temp, "ER", i+3) ||
                                            matches(temp, "EN", i+3)) {
                                            primary.append("X");
                                            secondary.append("SK");
                                        } else {
                                            primary.append("SK");
                                            secondary.append("SK");
                                        }
                                        i += 3;
                                        break;
                                    } else {
                                        if ((i == 0) && !isVowel(charAt(temp, 3))
                                            && !matches(temp, "W", i+3)) {
                                            primary.append("X");
                                            secondary.append("S");
                                        } else {
                                            primary.append("X");
                                            secondary.append("X");
                                        }
                                        i += 3;
                                        break;
                                    }
                                }

                                if (matches(temp, "I", i+2) ||
                                    matches(temp, "E", i+2) ||
                                    matches(temp, "Y", i+2)) {
                                    primary.append("S");
                                    secondary.append("S");
                                    i += 3;
                                    break;
                                }

                                // else
                                primary.append("SK");
                                secondary.append("SK");
                                i += 3;
                                break;
                            }

                            // french e.g. 'resnais', 'artois'
                            if (i == temp.length()-1 &&
                                   (matches(temp, "AI", i-2) || matches(temp, "OI", i-2))) {
                                primary.append("");
                                secondary.append("S");
                            } else {
                                primary.append("S");
                                secondary.append("S");
                            }

                            if (matches(temp, "S", i+1) ||
                                matches(temp, "Z", i+1)){
                                i += 2;
                            } else {
                                i++;
                            }
                            break;

                        case 'T':
                            if (matches(temp, "TION", i)) {
                                primary.append("X");
                                secondary.append("X");
                                i += 3;
                                break;
                            }

                            if (matches(temp, "TIA", i) ||
                                matches(temp, "TCH", i)) {
                                primary.append("X");
                                secondary.append("X");
                                i += 3;
                                break;
                            }

                            if (matches(temp, "TH",  i) ||
                                matches(temp, "TTH", i)) {
                                // special case 'thomas', 'thames' or germanic
                                if ((matches(temp, "OM", i+2) ||
                                     matches(temp, "AM", i+2))
                                 || (matches(temp, "VAN ", 0) ||
                                     matches(temp, "VON ", 0))
                                  || matches(temp, "SCH", 0)) {
                                    primary.append("T");
                                    secondary.append("T");
                                } else {
                                    primary.append("0");
                                    secondary.append("T");
                                }
                                i += 2;
                                break;
                            }

                            if (matches(temp, "T", i+1) ||
                                matches(temp, "D", i+1)) {
                                i += 2;
                            } else {
                                i++;
                            }
                            primary.append("T");
                            secondary.append("T");
                            break;

                        case 'V':
                            if (matches(temp, "V", i+1)) {
                                i += 2;
                            } else {
                                i++;
                            }
                            primary.append("F");
                            secondary.append("F");
                            break;

                        case 'W':
                            // can also be in middle of word
                            if (matches(temp, "WR", i)) {
                                primary.append("R");
                                secondary.append("R");
                                i += 2;
                                break;
                            }

                            if (i == 0 && (isVowel(charAt(temp, i+1))
                                || matches(temp, "WH", i))) {
                                // Wasserman should match Vasserman
                                if (isVowel(charAt(temp, i+1))) {
                                    primary.append("A");
                                    secondary.append("F");
                                } else {
                                    // need Uomo to match Womo
                                    primary.append("A");
                                    secondary.append("A");
                                }
                            }

                            // Arnow should match Arnoff
                            if (((i == temp.length()-1) && isVowel(charAt(temp, i-1)))
                                || (matches(temp, "EWSKI", i-1) ||
                                    matches(temp, "EWSKY", i-1) ||
                                    matches(temp, "OWSKI", i-1) ||
                                    matches(temp, "OWSKY", i-1))
                                || (matches(temp, "SCH", 0))) {
                                primary.append("");
                                secondary.append("F");
                                i++;
                                break;
                            }

                            // polish e.g. 'filipowicz'
                            if (matches(temp, "WICZ", i) ||
                                matches(temp, "WITZ", i)) {
                                primary.append("TS");
                                secondary.append("FX");
                                i += 4;
                                break;
                            }

                            // else skip it
                            i++;
                            break;

                        case 'X':
                            // french e.g. breaux
                            if (i == 0) {
                                primary.append("S");
                                secondary.append("S");
                                i++;
                            } else {
                                if (!((i == temp.length() - 1)
                                    && ((matches(temp, "IAU", i-3) ||
                                         matches(temp, "EAU", i-3))
                                    ||  (matches(temp, "AU", i-2) ||
                                         matches(temp, "OU", i-2))))) {
                                    primary.append("KS");
                                    secondary.append("KS");
                                }
                            }
                            if (matches(temp, "C", i+1) ||
                                matches(temp, "X", i+1)) {
                                i += 2;
                            } else {
                                i++;
                            }
                            break;

                        case 'Z':
                            // chinese pinyin e.g. 'zhao'
                            if (matches(temp, "H", i+1)) {
                                primary.append("J");
                                secondary.append("J");
                                i += 2;
                                break;
                            } else if ((matches(temp, "ZO", i+1) ||
                                        matches(temp, "ZI", i+1) ||
                                        matches(temp, "ZA", i+1))
                                || (germanic && ((i > 0)
                                && !matches(temp, "T", i-1)))) {
                                primary.append("S");
                                secondary.append("TS");
                            } else {
                                primary.append("S");
                                secondary.append("S");
                            }

                            if (matches(temp, "Z", i+1)) {
                                i += 2;
                            } else {
                                i++;
                            }
                            break;

                        default:
                            i++;
                    }
                }
                
                if (primary.length() > 4) {
                    result[0] = primary.toString().substring(0, 4);
                } else {
                    result[0] = primary.toString();
                }
                
                if (secondary.length() > 4) {
                    result[1] = secondary.toString().substring(0, 4);
                } else {
                    result[1] = secondary.toString();
                }
            }
        } catch (RuntimeException ex) {
            Logger.getLogger(DoubleMetaphone.class.getName()).log(Level.SEVERE, "s:" + s + " temp:" + temp + " result:" + Arrays.toString(result), ex);
            result = null;
        }

        return result;
    }

    private boolean isVowel(String vowel) {
        return "AEIOU".contains(vowel);
    }

    private String charAt(String s, int index) {
        String result = "";
        if (index >= 0 && index < s.length()) {
            result = "" + s.charAt(index);
        }
        return result;
    }

    private boolean matches(String s, String t, int start) {
        boolean result = false;
        if (start >= 0 && start <= s.length()) {
            String target = s.substring(start);

            if (target.startsWith(t)) {
                result = true;
            }
        }
        return result;
    }

    /**
     * This method compares two String using the Double Metaphone. If the
     * Strings produce the same encoding then the Strings are considered a
     * match and true is returned.
     * @param s input source String
     * @param t input target String
     * @return true if the source and target are considered a match, otherwise
     * false.
     */
    public boolean compareDoubleMetaphone(String s, String t){
        boolean flag = false;
        
        String [] sMetaphone = getDoubleMetaphone(s);
        String [] tMetaphone = getDoubleMetaphone(t);
        
        for (int i = 0; i < sMetaphone.length; i++){
            for (int j = 0; j < tMetaphone.length; j++){
                if (sMetaphone[i].equals(tMetaphone[j])){
                    flag = true;
                    break;
                }
            }
        }
        
        return flag;
    }

    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) {
        DoubleMetaphone dm = new DoubleMetaphone();
        System.out.format("%1$s   %2$s%n", Arrays.asList(dm.getDoubleMetaphone("Nelson")), Arrays.asList(dm.getDoubleMetaphone("Neilsen")));

        // "Occasionally" - "AKSN" and "AKXN"
        String [] hash = dm.getDoubleMetaphone("Occasionally");
        System.out.format("AKSN|AKXN   %1$s|%2$s%n", hash[0], hash[1]);

        // "antidisestablishmentarianism" - "ANTT"
        hash = dm.getDoubleMetaphone("antidisestablishmentarianism");
        System.out.format("ANTT   %1$s|%2$s%n", hash[0], hash[1]);

        // "appreciated" - "APRS" and "APRX"
        hash = dm.getDoubleMetaphone("appreciated");
        System.out.format("APRS|APRX   %1$s|%2$s%n", hash[0], hash[1]);

        // "beginning" - "PJNN" and "PKNN"
        hash = dm.getDoubleMetaphone("beginning");
        System.out.format("PJNN|PKNN   %1$s|%2$s%n", hash[0], hash[1]);

        // "changing" - "XNJN" and "XNKN"
        hash = dm.getDoubleMetaphone("changing");
        System.out.format("XNJN|XNKN   %1$s|%2$s%n", hash[0], hash[1]);

        // "cheat" - "XT"
        hash = dm.getDoubleMetaphone("cheat");
        System.out.format("XT   %1$s|%2$s%n", hash[0], hash[1]);

        // "dangerous" - "TNKR" and "TNJR"
        hash = dm.getDoubleMetaphone("dangerous");
        System.out.format("TNKR|TNJR   %1$s|%2$s%n", hash[0], hash[1]);

        // "development" - "TFLP"
        hash = dm.getDoubleMetaphone("development");
        System.out.format("TFLP   %1$s|%2$s%n", hash[0], hash[1]);

        // "etiology" - "ATLK" and "ATLJ"
        hash = dm.getDoubleMetaphone("etiology");
        System.out.format("ATLK|ATLJ   %1$s|%2$s%n", hash[0], hash[1]);

        // "existence" - "AKSS"
        hash = dm.getDoubleMetaphone("existence");
        System.out.format("AKSS   %1$s|%2$s%n", hash[0], hash[1]);

        // "simplicity" - "SMPL"
        hash = dm.getDoubleMetaphone("simplicity");
        System.out.format("SMPL   %1$s|%2$s%n", hash[0], hash[1]);

        // "circumstances" - "SRKM"
        hash = dm.getDoubleMetaphone("circumstances");
        System.out.format("SRKM   %1$s|%2$s%n", hash[0], hash[1]);

        // "fiery" - "FR"
        hash = dm.getDoubleMetaphone("fiery");
        System.out.format("FR   %1$s|%2$s%n", hash[0], hash[1]);

        // "february" - "FPRR"
        hash = dm.getDoubleMetaphone("february");
        System.out.format("FPRR   %1$s|%2$s%n", hash[0], hash[1]);

        // "illegitimate" - "ALJT" and "ALKT"
        hash = dm.getDoubleMetaphone("illegitimate");
        System.out.format("ALJT|ALKT   %1$s|%2$s%n", hash[0], hash[1]);

        // "immediately" - "AMTT"
        hash = dm.getDoubleMetaphone("immediately");
        System.out.format("AMTT   %1$s|%2$s%n", hash[0], hash[1]);

        // "happily" - "HPL"
        hash = dm.getDoubleMetaphone("happily");
        System.out.format("HPL   %1$s|%2$s%n", hash[0], hash[1]);

        // "judgment" - "JTKM" and "ATKM"
        hash = dm.getDoubleMetaphone("judgment");
        System.out.format("JTKM|ATKM   %1$s|%2$s%n", hash[0], hash[1]);

        // "knowing" - "NNK"
        hash = dm.getDoubleMetaphone("knowing");
        System.out.format("NNK   %1$s|%2$s%n", hash[0], hash[1]);

        // "kipper" - "KPR"
        hash = dm.getDoubleMetaphone("kipper");
        System.out.format("KPR   %1$s|%2$s%n", hash[0], hash[1]);

        // "john" - "JN" and "AN"
        hash = dm.getDoubleMetaphone("john");
        System.out.format("JN|AN   %1$s|%2$s%n", hash[0], hash[1]);

        // "lesion" - "LSN" and "LXN"
        hash = dm.getDoubleMetaphone("lesion");
        System.out.format("LSN|LXN   %1$s|%2$s%n", hash[0], hash[1]);

        // "Xavier" - "SF" and "SFR"
        hash = dm.getDoubleMetaphone("Xavier");
        System.out.format("SF|SFR   %1$s|%2$s%n", hash[0], hash[1]);

        // "dumb" - "TM"
        hash = dm.getDoubleMetaphone("dumb");
        System.out.format("TM   %1$s|%2$s%n", hash[0], hash[1]);

        // "caesar" - "SSR"
        hash = dm.getDoubleMetaphone("caesar");
        System.out.format("SSR   %1$s|%2$s%n", hash[0], hash[1]);

        // "chianti" - "KNT"
        hash = dm.getDoubleMetaphone("chianti");
        System.out.format("KNT   %1$s|%2$s%n", hash[0], hash[1]);

        // "michael" - "MKL" and "MXL"
        hash = dm.getDoubleMetaphone("michael");
        System.out.format("MKL|MXL   %1$s|%2$s%n", hash[0], hash[1]);

        // "chemistry" - "KMST"
        hash = dm.getDoubleMetaphone("chemistry");
        System.out.format("KMST   %1$s|%2$s%n", hash[0], hash[1]);

        // "chorus" - "KRS"
        hash = dm.getDoubleMetaphone("chorus");
        System.out.format("KRS   %1$s|%2$s%n", hash[0], hash[1]);

        // "architect - "ARKT"
        hash = dm.getDoubleMetaphone("architect");
        System.out.format("ARKT   %1$s|%2$s%n", hash[0], hash[1]);

        // "arch" - "ARX" and "ARK"
        hash = dm.getDoubleMetaphone("arch");
        System.out.format("ARX|ARK   %1$s|%2$s%n", hash[0], hash[1]);

        // "orchestra" - "ARKS"
        hash = dm.getDoubleMetaphone("orchestra");
        System.out.format("ARKS   %1$s|%2$s%n", hash[0], hash[1]);

        // "orchid" -  "ARKT"
        hash = dm.getDoubleMetaphone("orchid");
        System.out.format("ARKT   %1$s|%2$s%n", hash[0], hash[1]);

        // "wachtler" - "AKTL" and "FKTL"
        hash = dm.getDoubleMetaphone("wachtler");
        System.out.format("AKTL|FKTL   %1$s|%2$s%n", hash[0], hash[1]);

        // "wechsler" - "AKSL" and "FKSL"
        hash = dm.getDoubleMetaphone("wechsler");
        System.out.format("AKSL|FKSL   %1$s|%2$s%n", hash[0], hash[1]);

        // "tichner" - "TXNR" and "TKNR"
        hash = dm.getDoubleMetaphone("tichner");
        System.out.format("TXNR|TKNR   %1$s|%2$s%n", hash[0], hash[1]);

        // "McHugh" - "MK"
        hash = dm.getDoubleMetaphone("McHugh");
        System.out.format("MK   %1$s|%2$s%n", hash[0], hash[1]);

        // "czerny" - "SRN" and "XRN"
        hash = dm.getDoubleMetaphone("czerny");
        System.out.format("SRN|XRN   %1$s|%2$s%n", hash[0], hash[1]);

        // "focaccia" - "FKX"
        hash = dm.getDoubleMetaphone("focaccia");
        System.out.format("FKX   %1$s|%2$s%n", hash[0], hash[1]);

        // "bellocchio" - "PLX"
        hash = dm.getDoubleMetaphone("bellocchio");
        System.out.format("PLX   %1$s|%2$s%n", hash[0], hash[1]);

        // "bacchus" - "PKS"
        hash = dm.getDoubleMetaphone("bacchus");
        System.out.format("PKS   %1$s|%2$s%n", hash[0], hash[1]);

        // "accident" - "AKST"
        hash = dm.getDoubleMetaphone("accident");
        System.out.format("AKST   %1$s|%2$s%n", hash[0], hash[1]);

        // "accede" - "AKST"
        hash = dm.getDoubleMetaphone("accede");
        System.out.format("AKST   %1$s|%2$s%n", hash[0], hash[1]);

        // "succeed" - "SKST"
        hash = dm.getDoubleMetaphone("succeed");
        System.out.format("SKST   %1$s|%2$s%n", hash[0], hash[1]);

        // "bacci" - "PX"
        hash = dm.getDoubleMetaphone("bacci");
        System.out.format("PX   %1$s|%2$s%n", hash[0], hash[1]);

        // "bertucci" - "PRTX"
        hash = dm.getDoubleMetaphone("bertucci");
        System.out.format("PRTX   %1$s|%2$s%n", hash[0], hash[1]);

        // "mac caffrey" - "MKFR"
        hash = dm.getDoubleMetaphone("mac caffrey");
        System.out.format("MKFR   %1$s|%2$s%n", hash[0], hash[1]);

        // "mac gregor" - "MKRK"
        hash = dm.getDoubleMetaphone("mac gregor");
        System.out.format("MKRK   %1$s|%2$s%n", hash[0], hash[1]);

        // "edge" - "AJ"
        hash = dm.getDoubleMetaphone("edge");
        System.out.format("AJ   %1$s|%2$s%n", hash[0], hash[1]);

        // "edgar" - "ATKR"
        hash = dm.getDoubleMetaphone("edgar");
        System.out.format("ATKR   %1$s|%2$s%n", hash[0], hash[1]);

        // "ghislane" - "JLN"
        hash = dm.getDoubleMetaphone("ghislane");
        System.out.format("JLN   %1$s|%2$s%n", hash[0], hash[1]);

        // ghiradelli - "JRTL"
        hash = dm.getDoubleMetaphone("ghiradelli");
        System.out.format("JRTL   %1$s|%2$s%n", hash[0], hash[1]);

        // "hugh" - "H"
        hash = dm.getDoubleMetaphone("hugh");
        System.out.format("H   %1$s|%2$s%n", hash[0], hash[1]);

        // "bough" - "P"
        hash = dm.getDoubleMetaphone("bough");
        System.out.format("P   %1$s|%2$s%n", hash[0], hash[1]);

        // "broughton" - "PRTN"
        hash = dm.getDoubleMetaphone("broughton");
        System.out.format("PRTN   %1$s|%2$s%n", hash[0], hash[1]);

        // "laugh" - "LF"
        hash = dm.getDoubleMetaphone("laugh");
        System.out.format("LF   %1$s|%2$s%n", hash[0], hash[1]);

        // "McLaughlin" - "MKLF"
        hash = dm.getDoubleMetaphone("McLaughlin");
        System.out.format("MKLF   %1$s|%2$s%n", hash[0], hash[1]);

        // "cough" - "KF"
        hash = dm.getDoubleMetaphone("cough");
        System.out.format("KF   %1$s|%2$s%n", hash[0], hash[1]);

        // "gough" - "KF"
        hash = dm.getDoubleMetaphone("gough");
        System.out.format("KF   %1$s|%2$s%n", hash[0], hash[1]);

        // "rough" - "RF"
        hash = dm.getDoubleMetaphone("rough");
        System.out.format("RF   %1$s|%2$s%n", hash[0], hash[1]);

        // "tough" - "TF"
        hash = dm.getDoubleMetaphone("tough");
        System.out.format("TF   %1$s|%2$s%n", hash[0], hash[1]);

        // "cagney" - "KKN"
        hash = dm.getDoubleMetaphone("cagney");
        System.out.format("KKN   %1$s|%2$s%n", hash[0], hash[1]);

        // "tagliaro" - "TKLR" and "TLR"
        hash = dm.getDoubleMetaphone("tagliaro");
        System.out.format("TKLR|TLR   %1$s|%2$s%n", hash[0], hash[1]);

        // "biaggi" - "PJ" and "PK"
        hash = dm.getDoubleMetaphone("biaggi");
        System.out.format("PJ|PK   %1$s|%2$s%n", hash[0], hash[1]);

        // "san jacinto" - "SNHS"
        hash = dm.getDoubleMetaphone("san jacinto");
        System.out.format("SNHS   %1$s|%2$s%n", hash[0], hash[1]);

        // Yankelovich - "ANKL"
        hash = dm.getDoubleMetaphone("Yankelovich");
        System.out.format("ANKL   %1$s|%2$s%n", hash[0], hash[1]);

        // Jankelowicz - "JNKL" and "ANKL"
        hash = dm.getDoubleMetaphone("Jankelowicz");
        System.out.format("JNKL|ANKL   %1$s|%2$s%n", hash[0], hash[1]);

        // "bajador" - "PJTR" and "PHTR"
        hash = dm.getDoubleMetaphone("bajador");
        System.out.format("PJTR|PHTR   %1$s|%2$s%n", hash[0], hash[1]);

        // "cabrillo" - "KPRL" and "KPR"
        hash = dm.getDoubleMetaphone("cabrillo");
        System.out.format("KPRL|KPR   %1$s|%2$s%n", hash[0], hash[1]);

        // "gallegos" - "KLKS" and "KKS"
        hash = dm.getDoubleMetaphone("gallegos");
        System.out.format("KLKS|KKS   %1$s|%2$s%n", hash[0], hash[1]);

        // "dumb" - "TM"
        hash = dm.getDoubleMetaphone("dumb");
        System.out.format("TM   %1$s|%2$s%n", hash[0], hash[1]);

        // "thumb" - "0M" and "TM"
        hash = dm.getDoubleMetaphone("thumb");
        System.out.format("0M|TM   %1$s|%2$s%n", hash[0], hash[1]);

        // "campbell" - "KMPL"
        hash = dm.getDoubleMetaphone("campbell");
        System.out.format("KMPL   %1$s|%2$s%n", hash[0], hash[1]);

        // "raspberry" - "RSPR"
        hash = dm.getDoubleMetaphone("raspberry");
        System.out.format("RSPR   %1$s|%2$s%n", hash[0], hash[1]);

        // "hochmeier" - "HKMR"
        hash = dm.getDoubleMetaphone("hochmeier");
        System.out.format("HKMR   %1$s|%2$s%n", hash[0], hash[1]);

        // "island" - "ALNT"
        hash = dm.getDoubleMetaphone("island");
        System.out.format("ALNT   %1$s|%2$s%n", hash[0], hash[1]);

        // "isle" - "AL"
        hash = dm.getDoubleMetaphone("isle");
        System.out.format("AL   %1$s|%2$s%n", hash[0], hash[1]);

        // "carlisle" - "KRLL"
        hash = dm.getDoubleMetaphone("carlisle");
        System.out.format("KRLL   %1$s|%2$s%n", hash[0], hash[1]);

        // "carlysle" - "KRLL"
        hash = dm.getDoubleMetaphone("carlysle");
        System.out.format("KRLL   %1$s|%2$s%n", hash[0], hash[1]);

        // "smith" - "SM0" and "XMT"
        hash = dm.getDoubleMetaphone("smith");
        System.out.format("SM0|XMT   %1$s|%2$s%n", hash[0], hash[1]);

        // "schmidt" - "XMT" and "SMT"
        hash = dm.getDoubleMetaphone("schmidt");
        System.out.format("XMT|SMT   %1$s|%2$s%n", hash[0], hash[1]);

        // "snider" - "SNTR" and "XNTR"
        hash = dm.getDoubleMetaphone("snider");
        System.out.format("SNTR|XNTR   %1$s|%2$s%n", hash[0], hash[1]);

        // "schneider" - "XNTR" and "SNTR"
        hash = dm.getDoubleMetaphone("schneider");
        System.out.format("XNTR|SNTR   %1$s|%2$s%n", hash[0], hash[1]);

        // "school" - "SKL"
        hash = dm.getDoubleMetaphone("school");
        System.out.format("SKL   %1$s|%2$s%n", hash[0], hash[1]);

        // "schooner" - "SKNR"
        hash = dm.getDoubleMetaphone("schooner");
        System.out.format("SKNR   %1$s|%2$s%n", hash[0], hash[1]);

        // "schermerhorn" - "XRMR" and "SKRM"
        hash = dm.getDoubleMetaphone("schermerhorn");
        System.out.format("XRMR|SKRM   %1$s|%2$s%n", hash[0], hash[1]);

        // "schenker" - "XNKR" and "SKNK"
        hash = dm.getDoubleMetaphone("schenker");
        System.out.format("XNKR|SKNK   %1$s|%2$s%n", hash[0], hash[1]);

        // "resnais" - "RSN" and "RSNS"
        hash = dm.getDoubleMetaphone("resnais");
        System.out.format("RSN|RSNS   %1$s|%2$s%n", hash[0], hash[1]);

        // "artois" - "ART" and "ARTS"
        hash = dm.getDoubleMetaphone("artois");
        System.out.format("ART|ARTS   %1$s|%2$s%n", hash[0], hash[1]);

        // "thomas" - "TMS"
        hash = dm.getDoubleMetaphone("thomas");
        System.out.format("TMS   %1$s|%2$s%n", hash[0], hash[1]);

        // Wasserman - "ASRM" and "FSRM"
        hash = dm.getDoubleMetaphone("Wasserman");
        System.out.format("ASRM|FSRM   %1$s|%2$s%n", hash[0], hash[1]);

        // Vasserman - "FSRM"
        hash = dm.getDoubleMetaphone("Vasserman");
        System.out.format("FSRM   %1$s|%2$s%n", hash[0], hash[1]);

        // Uomo - "AM"
        hash = dm.getDoubleMetaphone("Uomo");
        System.out.format("AM   %1$s|%2$s%n", hash[0], hash[1]);

        // Womo - "AM" and "FM"
        hash = dm.getDoubleMetaphone("Womo");
        System.out.format("AM|FM   %1$s|%2$s%n", hash[0], hash[1]);

        // Arnow -  "ARN" and "ARNF"
        hash = dm.getDoubleMetaphone("Arnow");
        System.out.format("ARN|ARNF   %1$s|%2$s%n", hash[0], hash[1]);

        // Arnoff - "ARNF"
        hash = dm.getDoubleMetaphone("Arnoff");
        System.out.format("ARNF   %1$s|%2$s%n", hash[0], hash[1]);

        // "filipowicz" - "FLPT" and "FLPF"
        hash = dm.getDoubleMetaphone("filipowicz");
        System.out.format("FLPT|FLPF   %1$s|%2$s%n", hash[0], hash[1]);

        // breaux - "PR"
        hash = dm.getDoubleMetaphone("breaux");
        System.out.format("PR   %1$s|%2$s%n", hash[0], hash[1]);

        // "zhao" - "J"
        hash = dm.getDoubleMetaphone("zhao");
        System.out.format("J   %1$s|%2$s%n", hash[0], hash[1]);

        // "thames" - "TMS"
        hash = dm.getDoubleMetaphone("thames");
        System.out.format("TMS   %1$s|%2$s%n", hash[0], hash[1]);

        // a little different from the "DoubleMetaphone Test" results
        // at http://swoodbridge.com/DoubleMetaPhone/mptest.php3
        // ----------------------------------------------------------

        // "jose" - "JS" and "HS" (DoubleMetaphone Test got "HS" and "")
        hash = dm.getDoubleMetaphone("jose");
        System.out.format("JS|HS   %1$s|%2$s%n", hash[0], hash[1]);

        // "rogier" - "RJ" and "RKR" (DoubleMetaphone Test got "RJ" and "RJR" )
        hash = dm.getDoubleMetaphone("rogier");
        System.out.format("RJ|RKR   %1$s|%2$s%n", hash[0], hash[1]);

    }

}
