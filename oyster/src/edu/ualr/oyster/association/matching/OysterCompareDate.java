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

package edu.ualr.oyster.association.matching;

import edu.ualr.oyster.ErrorFormatter;
import edu.ualr.oyster.utilities.CharacterSubstringMatches;
import edu.ualr.oyster.utilities.OysterUtilityTranspose;
import edu.ualr.oyster.utilities.QGramTetrahedralRatio;
import java.text.ParseException;
import java.util.Calendar;
import java.util.Date;
import java.util.Locale;
import java.util.TimeZone;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Date Comparator class.
 * 
 * @author Eric D. Nelson
 */
public class OysterCompareDate extends OysterComparator{
    /** Single character transposition operator */
    private OysterUtilityTranspose transpose;
    
    /** Q-Gram Tetrahedral Ratio operator */
    private QGramTetrahedralRatio qGram;
    
    /** Substring operator */
    private CharacterSubstringMatches substr;
    
    /**
     * Creates a new instance of <code>OysterCompareDate</code>.
     */
    public OysterCompareDate () {
        super();
        
        String [] arr = {"TRANSPOSE", "QTR","SUBSTRLEFT","SUBSTRRIGHT","SUBSTRMID","WITHINDAYS","WITHINMONTHS","WITHINYEARS","DATEDIFF"};
        for (int i = 0; i < arr.length; i++){
            matchCodes.add(arr[i]);
            matchCodes.add("~"+arr[i]);
        }
        
        transpose = new OysterUtilityTranspose();
        qGram = new QGramTetrahedralRatio();
        substr = new CharacterSubstringMatches();
    }
    
    /**
     * Returns the match code for this <code>OysterCompareADEFirstName</code>.
     * @param s source String.
     * @param t target String.
     * @param matchType the type of match to preform.
     * @return the match code.
     */
    @Override
    public String getMatchCode (String s, String t, String matchType) {
        String result, tempMatchType = matchType;
        int length = 0, start = 0;
        float qTRThreshold = 0.25f;
        String pattern = "";
        boolean not = false;
        
        // Check for NOT operator
        if (matchType.toUpperCase(Locale.US).startsWith("~")){
            matchType = matchType.substring(1);
            not = true;
        }
        
        //======================================================================
        //  Get Funtionized arguments from Utilities
        //======================================================================
        if (matchType.toUpperCase(Locale.US).startsWith("SUBSTRLEFT(")){
            matchType = matchType.trim().substring(11, matchType.length()-1);
            
            length = Integer.parseInt(matchType);
            matchType = "SubStrLeft";
        } else if (matchType.toUpperCase(Locale.US).startsWith("SUBSTRRIGHT(")){
            matchType = matchType.trim().substring(12, matchType.length()-1);
            
            length = Integer.parseInt(matchType);
            matchType = "SubStrRight";
        } else if (matchType.toUpperCase(Locale.US).startsWith("SUBSTRMID(")){
            matchType = matchType.trim().substring(10, matchType.length()-1);
            String temp[] = matchType.split("[,]");
            
            start = Integer.parseInt(temp[0].trim());
            length = Integer.parseInt(temp[1].trim());
            
            matchType = "SubStrMid";
        } else if (matchType.toUpperCase(Locale.US).startsWith("QTR(")){
            matchType = matchType.trim().substring(4, matchType.length()-1);
            
            qTRThreshold = Float.parseFloat(matchType);
            matchType = "qTR";
        } else if (matchType.toUpperCase(Locale.US).startsWith("WITHINDAYS(")){
            matchType = matchType.trim().substring(11, matchType.length()-1);
            String temp[] = matchType.split("[,]");
            
            pattern = temp[0];
            length = Integer.parseInt(temp[1].trim());
            
            matchType = "WithinDays";
        } else if (matchType.toUpperCase(Locale.US).startsWith("WITHINMONTHS(")){
            matchType = matchType.trim().substring(13, matchType.length()-1);
            String temp[] = matchType.split("[,]");
            
            pattern = temp[0];
            length = Integer.parseInt(temp[1].trim());
            
            matchType = "WithinMonths";
        } else if (matchType.toUpperCase(Locale.US).startsWith("WITHINYEARS(")){
            matchType = matchType.trim().substring(12, matchType.length()-1);
            String temp[] = matchType.split("[,]");
            
            pattern = temp[0];
            length = Integer.parseInt(temp[1].trim());
            
            matchType = "WithinYears";
        } else if (matchType.toUpperCase(Locale.US).startsWith("DATEDIFF(")){
            matchType = matchType.trim().substring(9, matchType.length()-1);
            String temp[] = matchType.split("[,]");
            
            pattern = temp[0];
            length = Integer.parseInt(temp[1].trim());
            if (temp.length > 2) {
                start = Integer.parseInt(temp[2].trim());
            }
        
            matchType = "DateDiff";
        }
        
        //======================================================================
        //======================================================================
        if (!not) {
            if (matchType.equalsIgnoreCase("Transpose") && transpose.differByTranspose(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("qTR") && qGram.qTR(s, t) >= qTRThreshold) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrLeft") && substr.left(s, t, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrRight") && substr.right(s, t, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrMid") && substr.mid(s, t, start, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("WithinDays") && withinDays(s, t, pattern, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("WithinMonths") && withinMonths(s, t, pattern, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("WithinYears") && withinYears(s, t, pattern, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("DateDiff") && datediff(s, t, pattern, length, start)) {
                result = tempMatchType;
            } else {
                result = "X";
            } 
        } else {
            if (matchType.equalsIgnoreCase("Transpose") && !transpose.differByTranspose(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("qTR") && !(qGram.qTR(s, t) >= qTRThreshold)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrLeft") && !substr.left(s, t, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrRight") && !substr.right(s, t, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrMid") && !substr.mid(s, t, start, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("WithinDays") && !withinDays(s, t, pattern, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("WithinMonths") && !withinMonths(s, t, pattern, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("WithinYears") && !withinYears(s, t, pattern, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("DateDiff") && !(datediff(s, t, pattern, length, start))) {
                result = tempMatchType;
            } else {
                result = "X";
            }
        }
        return result.toUpperCase();
    }

    /**
     * This method returns whether the number of days between date s and date t
     * is of length days.
     * @param s the first date to compare.
     * @param t the second date to compare.
     * @param pattern the pattern that the string representation is using.
     * @param days the number of days to be validated against
     * @return true if the two dates are less than or equal to the length,
     * otherwise false.
     */
    private boolean withinDays(String s, String t, String pattern, int days) {
        boolean flag = false;

        try {
            Calendar cs = Calendar.getInstance();
            cs.setTime(stringToDate(s, pattern));

            Calendar ct = Calendar.getInstance();
            ct.setTime(stringToDate(t, pattern));

            int min = Math.min(cs.get(Calendar.YEAR), ct.get(Calendar.YEAR));
            int ds = daysSinceMinYear(cs, min);
            int dt = daysSinceMinYear(ct, min);

            if (Math.abs(ds - dt) <= days) {
                flag = true;
            }
        } catch (RuntimeException ex) {
            Logger.getLogger(OysterCompareDate.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return flag;
    }
    
    /**
     * This method returns whether the number of months between date s and date t
     * is of length l.
     * @param s the first date to compare.
     * @param t the second date to compare.
     * @param pattern the pattern that the string representation is using.
     * @param months the number of months to be validated against
     * @return true if the two dates are less than or equal to the length,
     * otherwise false.
     */
    private boolean withinMonths(String s, String t, String pattern, int months) {
        boolean flag = false;
        try {
            Calendar cs = Calendar.getInstance();
            cs.setTime(stringToDate(s, pattern));

            Calendar ct = Calendar.getInstance();
            ct.setTime(stringToDate(t, pattern));

            int min = Math.min(cs.get(Calendar.YEAR), ct.get(Calendar.YEAR));
            int ds = monthsSinceMinYear(cs, min);
            int dt = monthsSinceMinYear(ct, min);

            if (Math.abs(ds - dt) <= months) {
                flag = true;
            }
        } catch (RuntimeException ex) {
            Logger.getLogger(OysterCompareDate.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return flag;
    }
    
    /**
     * This method returns whether the number of years between date s and date t
     * is of length l.
     * @param s the first date to compare.
     * @param t the second date to compare.
     * @param pattern the pattern that the string representation is using.
     * @param years the number of years to be validated against
     * @return true if the two dates are less than or equal to the length,
     * otherwise false.
     */
    private boolean withinYears(String s, String t, String pattern, int years) {
        boolean flag = false;
        try {
            Calendar cs = Calendar.getInstance();
            cs.setTime(stringToDate(s, pattern));

            Calendar ct = Calendar.getInstance();
            ct.setTime(stringToDate(t, pattern));

            if (Math.abs(cs.get(Calendar.YEAR) - ct.get(Calendar.YEAR)) <= years) {
                flag = true;
            }
        } catch (RuntimeException ex) {
            Logger.getLogger(OysterCompareDate.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return flag;
    }
    
    private boolean datediff(String s, String t, String pattern, int length, int mode) {
        boolean flag = false;
        long diff;

        try {
            Calendar cs = Calendar.getInstance();
            cs.setTime(stringToDate(s, pattern));

            Calendar ct = Calendar.getInstance();
            ct.setTime(stringToDate(t, pattern));

            long millsec = Math.abs(cs.getTimeInMillis() - ct.getTimeInMillis());
            
            switch (mode){
                case 0: // days
                    diff = millsec / 1000  / 60 / 60 /24;
                    break;
                case 1: // months
                    diff = millsec / 1000  / 60 / 60 /24 /30;
                    break;
                case 2: // years
                    diff = millsec / 1000  / 60 / 60 /24 /365;
                    break;
                default: diff = millsec / 1000  / 60 / 60 /24;
            }
            
            if (diff <= length) {
                flag = true;
            }
        } catch (RuntimeException ex) {
            Logger.getLogger(OysterCompareDate.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return flag;
    }
    
    /**
     * This method returns the number of days since the calendar date.
     * @param cal the date to be checked
     * @param min the day to start counting
     * @return the number of minimum days.
     */
    private int daysSinceMinYear(Calendar cal, int min) {
        int days = -1;
        
        if (cal != null){
            days = 0;
            
            // get the number of days for each year
            for (int i = min; i < cal.get(Calendar.YEAR); i++){
                if (isLeapYear(i)) {
                    days += 366;
                } else {
                    days += 365;
                }
            }
            
            /*
            // get the number of days for each month
            for (int i = 0; i < cal.get(Calendar.YEAR); i++){
                switch(i){
                    case 0: days += cal.getMaximum(Calendar.JANUARY); break;
                    case 1: if (isLeapYear(cal.get(Calendar.YEAR)))
                                days += 29;
                            else days += 28;
                            break;
                    case 2: days += cal.getMaximum(Calendar.MARCH); break;
                    case 3: days += cal.getMaximum(Calendar.APRIL); break;
                    case 4: days += cal.getMaximum(Calendar.MAY); break;
                    case 5: days += cal.getMaximum(Calendar.JUNE); break;
                    case 6: days += cal.getMaximum(Calendar.JULY); break;
                    case 7: days += cal.getMaximum(Calendar.AUGUST); break;
                    case 8: days += cal.getMaximum(Calendar.SEPTEMBER); break;
                    case 9: days += cal.getMaximum(Calendar.OCTOBER); break;
                    case 10: days += cal.getMaximum(Calendar.NOVEMBER); break;
                    case 11: days += cal.getMaximum(Calendar.DECEMBER); break;
                }
            }
            
            // get the days in this month
            cal.
            */
            
            days += cal.get(Calendar.DAY_OF_YEAR);
        }
        
        return days;
    }
    
    /**
     * This method returns the number of months since the calendar date.
     * @param cal the date to be checked
     * @param min the month to start counting
     * @return the number of minimum months.
     */
    private int monthsSinceMinYear(Calendar cal, int min) {
        int months = -1;
        
        if (cal != null){
            months = 0;
            
            // get the number of days for each year
            for (int i = min; i < cal.get(Calendar.YEAR); i++){
                months += 12;
            }
        
        // months are zero based so must add a one, i.e. January = 0.
        months += cal.get(Calendar.MONTH) + 1;
        }

        return months;
    }
    
    /**
     * This method returns that Date object for the input string and pattern.
     * @param date the String representation of the date
     * @param pattern the pattern the string date is in
     * @return the Date for the input string
     */
    private Date stringToDate(String date, String pattern){
        java.util.Date result = null;
        try {
            java.text.SimpleDateFormat sdf = new java.text.SimpleDateFormat(pattern);
            sdf.setTimeZone(TimeZone.getDefault());
            
            result = sdf.parse(date);
        } catch (ParseException ex) {
            Logger.getLogger(OysterCompareDate.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return result;
    }
    
    /**
     * This method determines if a year is a leap year.
     * @param year the year
     * @return true if the input year is a leap year, otherwise false.
     */
    private boolean isLeapYear(int year){
        boolean flag = false;
        if (year % 4 == 0 && year % 400 == 0) {
            flag = true;
        }
        return flag;
    }
}
