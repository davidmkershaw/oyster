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
 * The Smith–Waterman algorithm is a well-known algorithm for performing local 
 * sequence alignment; that is, for determining similar regions between two 
 * nucleotide or protein sequences. Instead of looking at the total sequence, 
 * the Smith–Waterman algorithm compares segments of all possible lengths and 
 * optimizes the similarity measure.
 * 
 * (Excerpt taken from Wikipedia)
 * 
 * References:
 * <ul>
 * <li>Smith TF, Waterman MS. Identification of common molecular subsequences. 
 *   J Mol Biol. 1981 Mar 25;147(1):195-7. </li>
 * <li>Gotoh O. An improved algorithm for matching biological sequences. 
 *   J Mol Biol. 1982 Dec 15;162(3):705-8. </li>
 *  </ul>
 * 
 * @see http://en.wikipedia.org/wiki/Smith%E2%80%93Waterman_algorithm
 * @see http://www.clcbio.com/index.php?id=1046
 * Created on Jun 20, 2012 9:44:13 PM
 * @author Eric. D Nelson
 */
public class SmithWaterman {
    /** The calculated distance between the two strings */
    private float distance = 0;

    /** The length of the longer string */
    private int lengthOfLong = 0;
    
    /** Workspace */
    private float [][] matrix = null;
    
    /** Resulting Alignments */
    private String sequence1 = "", sequence2 = "";
    
    /**
     * Creates a new instance of SmithWaterman
     */
    public SmithWaterman(){
    }

    public float computeSmithWaterman(String s, String t, float match, float mismatch, float gap) {
        float result = 0;
//        System.out.println();
        
        if (s == null && t == null){
            lengthOfLong = 0;
        }
        else if (s == null && t != null){
            lengthOfLong = t.length();
        }
        else if (s != null && t == null){
            lengthOfLong = s.length();
        }
        else if (s != null && t != null){
            String sTemp = s.toUpperCase(Locale.US);
            String tTemp = t.toUpperCase(Locale.US);
            
            lengthOfLong = Math.max(tTemp.length(), sTemp.length());
            
            // create the matrix
            matrix = new float[tTemp.length()+1][sTemp.length()+1];
            
            // fill it with zeros
            for (int i = 0; i < tTemp.length(); i++) {
                Arrays.fill(matrix[i], 0.0f);
            }
            
            // compute the value for each cell
            int [] start = new int[2];
            float check = 0;
            for (int i = 1; i <= tTemp.length(); i++) {
                for (int j = 1; j <= sTemp.length(); j++) {
//                    System.out.println("Matrix[" + i + "]" + "[" + j + "]");
//                    System.out.println("char @ " + (i-1) + ": " + tTemp.charAt(i-1));
//                    System.out.println("char @ " + (j-1) + ": " + sTemp.charAt(j-1));
                    // do the characters match?
                    if (tTemp.charAt(i-1) == sTemp.charAt(j-1)){
                        matrix[i][j] = matrix[i-1][j-1] + match;
//                        System.out.println("Match   : " + matrix[i][j]);
                    }
                    else {
                        float diag = matrix[i-1][j-1] + mismatch;
                        float top = matrix[i-1][j] + gap;
                        float left = matrix[i][j-1] + gap;
                        
                        float max = Math.max(diag, top);
                        max = Math.max(max, left);
                        max = Math.max(max, 0);
                        
                        matrix[i][j] = max;
//                        System.out.println("Nonmatch: " + matrix[i][j]);
                    }
                    
                    // Check for the max
                    if (matrix[i][j] > check){
                        start[0] = i;
                        start[1] = j;
                        check = matrix[i][j];
                    }
//                    System.out.println();
                }
            }
            
//            outputMatrix();
            
            sequence1 = sequence2 = ""; 
            // backtrack for alignment
            int i = start[0];
            int j = start[1];
            
            while (true){
                float current = matrix[i][j];

                if (current <= 0) {
                    break;
                }

                float diag = matrix[i - 1][j - 1];
                float top = matrix[i - 1][j];
                float left = matrix[i][j - 1];
                
                // diag - the letters from two sequences are aligned
                // left - a gap is introduced in the left sequence
                // top  - a gap is introduced in the top sequence
                if (diag >= top && diag >= left) {
                    sequence1 = sTemp.charAt(j - 1) + sequence1;
                    sequence2 = tTemp.charAt(i - 1) + sequence2;
                    i--;
                    j--;
                } else if (left >= diag && left >= top) {
                    sequence1 = sTemp.charAt(j - 1) + sequence1;
                    sequence2 = "-" + sequence2;
                    j--;
                } else if (top >= diag && top >= left) {
                    sequence1 = "-" + sequence1;
                    sequence2 = tTemp.charAt(i - 1) + sequence2;
                    i--;
                }
            }
/*
            System.out.println("Input    :");
            System.out.println("\t" + s);
            System.out.println("\t" + t);
            System.out.println("Alignment:");
            System.out.println("\t" + sequence1);
            System.out.println("\t" + sequence2);
*/
            result = matrix[start[0]][start[1]];
        }
        
        distance = result;
        return result;
    }

    public float computeNormalizedScore () {
        float norm;
        float maxLen = lengthOfLong;

        norm = 1f - ((float) distance / (maxLen * distance));

        return norm;
    }
    
    public float computeNormalizedScore2 () {
        float norm;
        
        int gaps = Math.max(sequence1.split("[-]").length-1, sequence2.split("[-]").length-1);
        float maxLen = lengthOfLong;
        norm = 1f - ((float)gaps  / (float)distance);
        
        return norm;
    }

    public void outputMatrix(){
        if (matrix != null) {
            for (int i = 0; i < matrix.length; i++){
                for (int j = 0; j < matrix[i].length; j++) {
                    System.out.print(matrix[i][j] + "\t");
                }
                System.out.println();
            }
        }
    }
    
    /**
     * @param args the command line arguments
     */
/*
    public static void main(String[] args) {
        SmithWaterman sw = new SmithWaterman();
        // Sequence 1 = A-CACACTA
        // Sequence 2 = AGCACAC-A
        String s = "ACACACTA";
        String t = "AGCACACA";
        float match = sw.computeSmithWaterman(s, t, 2, -1, -1);
        System.out.println("S       : " + s);
        System.out.println("T       : " + t);
        System.out.println("Score   : " + match);
        System.out.println("N-Score: " +sw.computeNormalizedScore());
        System.out.println("N-Score2: " + sw.computeNormalizedScore2());
        System.out.println();
        
        s = "CORDACORPRETADIAMETRO95MMDUREZA75SHOREFORMATOREDONDOMATERIALBORRACHANITRILICABUNAN";
        t = "CORDACORPRETADIAMETRO65MMDUREZA75SHOREAFORMATOREDONDOMATERIALBORRACHANITRILICABUNAN";
        match = sw.computeSmithWaterman(s, t, 1, 0, 0);
        System.out.println("S       : " + s);
        System.out.println("T       : " + t);
        System.out.println("Score   : " + match);
        System.out.println("N-Score : " + sw.computeNormalizedScore());
        System.out.println("N-Score2: " + sw.computeNormalizedScore2());
        System.out.println();
        
        s = "cgggtatccaa";
        t = "ccctaggtccca";
        match = sw.computeSmithWaterman(s, t, 1, -1, -1);
        System.out.println("S       : " + s);
        System.out.println("T       : " + t);
        System.out.println("Score   : " + match);
        System.out.println("N-Score : " + sw.computeNormalizedScore());
        System.out.println("N-Score2: " + sw.computeNormalizedScore2());
        System.out.println();
        
        s = "ACTGAACTG";
        t = "ATGGACCTG";
        match = sw.computeSmithWaterman(s, t, 1, 0.33F, -1);
        System.out.println("S       : " + s);
        System.out.println("T       : " + t);
        System.out.println("Score   : " + match);
        System.out.println("N-Score: " +sw.computeNormalizedScore());
        System.out.println("N-Score2: " + sw.computeNormalizedScore2());
        System.out.println();
        
        s = "CTGG";
        t = "CATTG";
        match = sw.computeSmithWaterman(s, t, 10, -3, -3);
        System.out.println("S       : " + s);
        System.out.println("T       : " + t);
        System.out.println("Score   : " + match);
        System.out.println("N-Score : " + sw.computeNormalizedScore());
        System.out.println("N-Score2: " + sw.computeNormalizedScore2());
        System.out.println();
        
        s = "2801 South University, Little Rock";
        t = "2801 S. Univers., Little Rock";
        match = sw.computeSmithWaterman(s, t, 5, -1, -3);
        System.out.println("S       : " + s);
        System.out.println("T       : " + t);
        System.out.println("Score   : " + match);
        System.out.println("N-Score : " + sw.computeNormalizedScore());
        System.out.println("N-Score2: " + sw.computeNormalizedScore2());
    }
*/
}
