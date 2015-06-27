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

package edu.ualr.oyster.optimization;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Oyster is a rule based engine. It is possible that the same element can appear
 * in multiple rules with multiple operations. In table 3 below, Last name appears
 * in all 8 rules. It also must be an exact match in each rule. If 10,000 records
 * were compared potentially 80,000 comparisons would have to be made on the last
 * name alone. Comparing the same elements multiple times doesn’t produce different
 * results it only wastes computation cycles. Because of this there is an obvious
 * need for some type of optimization capability to keep the comparisons to a 
 * reasonable level. A very simple method was found to optimize the rule list. 
 * This was through the use of a matrix. First a two dimensional boolean matrix 
 * of unique elements X unique operations is created. This is the base rule 
 * matrix.  From this base matrix a rule matrix is cloned, one for each rule. 
 * For each mask a true value is set for the cell corresponding to the element 
 * and operations within that rule.
 * @author Eric D. Nelson
 */
public class Matrix implements Cloneable{
    /** The data matrix */
    private boolean [][] matrix;

    /** The matrix rows (attribute) */
    private Map<String, Integer> rows = new LinkedHashMap<String, Integer>();

    /** The matrix columns (match result)*/
    private Map<String, Integer> columns = new LinkedHashMap<String, Integer>();
    
    /**
     * Creates a new Matrix of <code>Matrix</code>
     */
    public Matrix(){
    }

    /**
     * Creates a new Matrix of <code>Matrix</code>
     * @param rows the number of rows in the matrix
     * @param columns the number of columns in the matrix
     */
    public Matrix(int rows, int columns){
        matrix = new boolean[rows][columns];
        this.fill(false);
    }
    
    /**
     * Returns the data matrix for this <code>Matrix</code>.
     * @return the data matrix
     */
    public boolean[][] getMatrix() {
        return matrix.clone();
    }

    /**
     * Sets the data matrix for this <code>Matrix</code>.
     * @param matrix the matrix to be set
     */
    public void setMatrix(boolean[][] matrix) {
        if (this.matrix == null) {
            this.matrix = new boolean[matrix.length][matrix[0].length];
        }
        System.arraycopy(matrix, 0, this.matrix, 0, matrix.length);
    }

    /**
     * Returns the rows for this <code>Matrix</code>.
     * @return the rows
     */
    public Map<String, Integer> getRows() {
        return rows;
    }

    /**
     * Sets the rows matrix for this <code>Matrix</code>.
     * @param rows the rows to be set
     */
    public void setRows(Map<String, Integer> rows) {
        this.rows = rows;
    }

    /**
     * Returns the columns for this <code>Matrix</code>.
     * @return the columns
     */
    public Map<String, Integer> getColumns() {
        return columns;
    }

    /**
     * Sets the columns matrix for this <code>Matrix</code>.
     * @param columns the columns to be set
     */
    public void setColumns(Map<String, Integer> columns) {
        this.columns = columns;
    }

    /**
     * Fills the data matrix with boolean value b.
     * @param b the boolean value to set the matrix.
     */
    public final void fill(boolean b) {
        for (int i = 0; i < rows.size(); i++){
            Arrays.fill(matrix[i], b);
        }
    }
    
    /**
     * Returns a clone of this Matrix. The clone will contain a
     * copy of the internal data array.
     *
     * @return  a clone of this Matrix
     */
    @Override
    public synchronized Object clone() throws CloneNotSupportedException{
        super.clone();
        
        Matrix m = new Matrix();
        m.setColumns(this.columns);
        m.setRows(this.rows);
        m.setMatrix(new boolean[this.rows.size()][this.columns.size()]);
        
        for (int i = 0; i < this.rows.size(); i++){
            System.arraycopy(this.matrix[i], 0, m.matrix[i], 0, this.columns.size());
        }
        return m;
    }
    
    /**
     * Returns a hash code value for the object. This method is 
     * supported for the benefit of HashTables such as those provided by 
     * <code>java.util.Hashtable</code>. 
     * @return a hash code value for this object.
     */
    @Override
    public int hashCode() {
        int hash = 3;
        hash = 53 * hash + (this.matrix != null ? java.util.Arrays.hashCode(this.matrix) : 0);
        hash = 53 * hash + (this.rows != null ? this.rows.hashCode() : 0);
        hash = 53 * hash + (this.columns != null ? this.columns.hashCode() : 0);
        return hash;
    }

    /**
     * Indicates whether some other object is "equal to" this one.
     * @param obj the reference object with which to compare.
     * @return <code>true</code> if this object is the same as the obj
     *          argument; <code>false</code> otherwise.
     */
    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        
        if (getClass() != obj.getClass()) {
            return false;
        }
        
        final Matrix other = (Matrix) obj;
        if (this == null && other != null) {
            return false;
        }
        
        if ((this.rows == null || !this.rows.equals(other.rows)) && this.rows != other.rows) {
            return false;
        }
        
        if ((this.columns == null || !this.columns.equals(other.columns)) && this.columns != other.columns) {
            return false;
        }
        
        for (int i = 0; i < rows.size(); i++) {
            for (int j = 0; j < columns.size(); j++) {
                if (this.matrix[i][j] != other.matrix[i][j]) {
                    return false;
                }
            }
        }
        
        return true;
    }
    
    /**
     * Returns a string representation of the <code>Matrix</code>.
     * @return a string representation of this object.
     */
    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();
        sb.append("\t");
        Object [] cols =  columns.keySet().toArray();
        for (int j = 0; j < cols.length; j++){
            sb.append(cols[j]).append("\t");
        }
        sb.append(System.getProperty("line.separator"));
        
        Object [] rs = rows.keySet().toArray();
        for (int i = 0; i < rs.length; i++){
            sb.append(rs[i]).append("\t");
            for (int j = 0; j < cols.length; j++){
                sb.append(matrix[i][j]).append("\t");
            }
            sb.append(System.getProperty("line.separator"));
        }
        return sb.toString();
    }
}
