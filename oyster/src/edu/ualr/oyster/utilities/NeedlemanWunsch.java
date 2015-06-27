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

import java.util.Locale;

/**
 * The Needleman–Wunsch algorithm performs a global alignment on two sequences 
 * (called A and B here). It is commonly used in bioinformatics to align protein
 * or nucleotide sequences. The algorithm was published in 1970 by Saul B. 
 * Needleman and Christian D. Wunsch.[1]
 * 
 * (Excerpt taken from Wikipedia)
 * 
 * References:
 * <ul>
 * <li>Needleman, Saul B.; and Wunsch, Christian D. (1970). "A general method 
 * applicable to the search for similarities in the amino acid sequence of 
 * two proteins". Journal of Molecular Biology 48 (3): 443–53. </li>
 * <li></li>
 * </ul>
 * Created on Jun 20, 2012 9:44:43 PM
 * @author Eric. D Nelson
 */
public class NeedlemanWunsch {
    /** The calculated distance between the two strings */
    private float distance = 0;

    /** The length of the longer string */
    private int lengthOfLong = 0;
    
    /** Workspace */
    private float [][] matrix = null;
    
    /** Similarity matrix */
    public int[][] simularity;
    
    /** Resulting Alignments */
    private String sequence1 = "", sequence2 = "";
    
    /**
     * Creates a new instance of NeedlemanWunsch
     */
    public NeedlemanWunsch(){
    }

    // FIXME: Does not give the same answer as examples, not sure why
    public float computeNeedlemanWunsch(String s, String t, float match, float mismatch, float gap) {
        float result = 0;
        System.out.println();
        lengthOfLong = 0;
        if (s == null && t == null){
            
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
            
            // calculate the first row and column
            for (int i = 0; i < tTemp.length()+1; i++) {
                matrix[i][0] = gap * i;
            }
            for (int j = 0; j < sTemp.length()+1; j++) {
                matrix[0][j] = gap * j;
            }
            
            // compute the value for each cell
            for (int i = 1; i <= tTemp.length(); i++) {
                for (int j = 1; j <= sTemp.length(); j++) {
                    System.out.println("Matrix[" + i + "]" + "[" + j + "]");
                    System.out.println("char @ " + (i-1) + ": " + tTemp.charAt(i-1));
                    System.out.println("char @ " + (j-1) + ": " + sTemp.charAt(j-1));
                    // do the characters match?
                    if (tTemp.charAt(i-1) == sTemp.charAt(j-1)){
                        // Match ← F(i-1,j-1) + S(Ai, Bj)
                        matrix[i][j] = matrix[i-1][j-1] + match;
                        System.out.println("Match   : " + matrix[i][j]);
                    }
                    else {
                        float diag = matrix[i-1][j-1] + mismatch;
                        // Delete ← F(i-1, j) + d
                        float top =    matrix[i-1][j] + gap;
                        // Insert ← F(i, j-1) + d
                        float left = matrix[i][j-1] + gap;
                        
                        float max = Math.max(diag, top);
                        max = Math.max(max, left);
                        
                        matrix[i][j] = max;
                        System.out.println("Nonmatch: " + matrix[i][j]);
                    }
                    System.out.println();
                }
            }
            
            outputMatrix();
            
            // backtrack for alignment
            boolean stop = false;
            int i = tTemp.length();
            int j = sTemp.length();
            
            while (i > 0 && j > 0){
                float score = matrix[i][j];
                float diag = matrix[i - 1][j - 1];
                float up = matrix[i][j - 1];
                float left = matrix[i - 1][j];
                
                // FIXME: Need to change to use BigDecimal @see http://findbugs.sourceforge.net/bugDescriptions.html#FE_FLOATING_POINT_EQUALITY
                if (score == diag + match){
                    sequence1 = sTemp.charAt(j - 1) + sequence1;
                    sequence2 = tTemp.charAt(i - 1) + sequence2;
                    i--;
                    j--;
                }
                else if (score == left + gap) {
                    sequence1 = "-" + sequence1;
                    sequence2 = tTemp.charAt(i - 1) + sequence2;
                    i--;
                }
                else if (score == up + gap) {
                    sequence1 = sTemp.charAt(j - 1) + sequence1;
                    sequence2 = "-" + sequence2;
                    j--;
                }
            }
  
            while (i > 0) {
                sequence1 = "-" + sequence1;
                sequence2 = tTemp.charAt(i - 1) + sequence2;
                i--;
            }
  
            while (j > 0) {
                sequence1 = sTemp.charAt(j - 1) + sequence1;
                sequence2 = "-" + sequence2;
                j--;
            }
            
            System.out.println("Input    :");
            System.out.println("\t" + s);
            System.out.println("\t" + t);
            System.out.println("Alignment:");
            System.out.println("\t" + sequence1);
            System.out.println("\t" + sequence2);
//            result = matrix[start[0]][start[1]];
        }
        
        distance = result;
        return result;
    }

    public float computeNormalizedScore (float match) {
        float norm;
        float maxLen = lengthOfLong;
        norm = Math.max(distance, 0f)/(maxLen * match);
        return norm;
    }
    
    public float computeNormalizedScore2 () {
        float norm;
        
        int gaps = Math.max(sequence1.split("[-]").length-1, sequence2.split("[-]").length-1);
        float maxLen = lengthOfLong;
        norm = 1f - ((float)gaps / maxLen);
        
        return norm;
    }

    private void outputMatrix(){
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
    public static void main(String[] args) {
        int match = 10, mismatch = -1, gap = -5;
        NeedlemanWunsch sw = new NeedlemanWunsch();
        // Sequence 1 = A-CACACTA
        // Sequence 2 = AGCACAC-A
        System.out.println("Score  : " + sw.computeNeedlemanWunsch("AGCT", "AGCT", match, mismatch, gap));
        System.out.println("N-Score: " +sw.computeNormalizedScore(match));
    }

}
