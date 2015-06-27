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
 * 
 * Threshold is >= 0.25 but it can be adjusted by the user.
 * 
 * For more information see http://www.gregholland.com/greg/academics.asp
 * ALAR Preceeding 2010
 * @author Eric D. Nelson
 */
public class QGramTetrahedralRatio {
    /**
     * Creates a new instance of <code>QGramTetrahedralRatio</code>
     */
    public QGramTetrahedralRatio () {
    }

    /**
     * 
     * @param s1 String one
     * @param s2 String two
     * @return result
     */
    public float qTR(String s1, String s2){
        float result = -1;
        int i = 0, j;
        float Q = 0;
        boolean quit = false;
        
        if (s1 != null && s2 != null && s1.length() > 0 && s2.length() > 0) {
            while (i <= s1.length()){
                j = i;
                while (j < s1.length() +1){
                    if ((s2.toLowerCase(Locale.US).indexOf(s1.toLowerCase(Locale.US).substring(i, j))) > -1 &&
                         !s1.toLowerCase(Locale.US).substring(i, j).equals("")){
//                        System.out.println(s1.toLowerCase(Locale.US).substring(i, j));
                        Q += j - i;
                    }
/*                    
                    else {
                        j = s1.length() + 1;
                        quit = true;
                    }
*/
                    j++;
                }
                i++;
            }
            
            if (!quit){
                float n1 = s1.length();
                float n2 = s2.length();
                float Tn1 = (n1) * (n1 + 1) * (n1 + 2)/ 6f;
                float Tn2 = (n2) * (n2 + 1) * (n2 + 2) / 6f;
                result = (n1 * Q / Tn1 + n2 * Q / Tn2) / (n1 + n2);
//                System.out.println(Q);
            }
            
        }
        return result;
    }
    
    public float qTRCyclic(String s1, String s2){
        float result = -1;
        int i = 0, j;
        float Q = 0;
        
        if (s1 != null && s2 != null && s1.length() > 0 && s2.length() > 0) {
            s1 = s1 + s1;
            s2 = s2 + s2;
            while (i <= s1.length()/2){
                j = i;
                while (j < s1.length() +1){
                    if ((s2.toLowerCase(Locale.US).indexOf(s1.toLowerCase(Locale.US).substring(i, j))) > -1 &&
                         !s1.toLowerCase(Locale.US).substring(i, j).equals("")){
//                        System.out.println(s1.toLowerCase(Locale.US).substring(i, j));
                        Q += j - i;
                    }
                    j++;
                }
                i++;
            }
            float n1 = s1.length()-1;
            float n2 = s2.length()-1;
            float Tn1 = (n1) * (n1 + 1) * (n1 + 2)/ 6f;
            float Tn2 = (n2) * (n2 + 1) * (n2 + 2) / 6f;
            result = (n1 * Q / Tn1 + n2 * Q / Tn2) / (n1 + n2);
//            System.out.println(Q);
        }
        return result;
    }
    
    /**
     * @param args the command line arguments
     */
/*    public static void main(String[] args) {
        String in = "J:\\Oyster\\qTR_examples.txt",
               out = "J:\\Oyster\\qTR_examples.out",
               read;
        String [] text;
        try{
            QGramTetrahedralRatio q = new QGramTetrahedralRatio();

            BufferedReader infile = new BufferedReader(new FileReader(in));
            PrintWriter outfile = new PrintWriter(new OutputStreamWriter(new FileOutputStream(out)));
            
            while((read = infile.readLine()) != null){
                text = read.split("[\t]");
                
                float result = q.qTR(text[0], text[1]);
                outfile.println(text[0] + "\t" + text[1] + "\t" + text[2] + "\t" + result);
            }
            outfile.close();
            infile.close();
        }
        catch(Exception e){
            System.err.println(e.getMessage());
        }
    } */
}
