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

import edu.ualr.oyster.utilities.Caverphone;
import edu.ualr.oyster.utilities.Caverphone2;
import edu.ualr.oyster.utilities.CharacterSubstringMatches;
import edu.ualr.oyster.utilities.DaitchMokotoffSoundex;
import edu.ualr.oyster.utilities.DoubleMetaphone;
import edu.ualr.oyster.utilities.IBMAlphaCode;
import edu.ualr.oyster.utilities.Jaccard;
import edu.ualr.oyster.utilities.MatchRatingApproach;
import edu.ualr.oyster.utilities.Metaphone;
import edu.ualr.oyster.utilities.NYSIISCode;
import edu.ualr.oyster.utilities.OysterEditDistance;
import edu.ualr.oyster.utilities.OysterNickNameTable;
import edu.ualr.oyster.utilities.OysterUtilityTranspose;
import edu.ualr.oyster.utilities.QGramTetrahedralRatio;
import edu.ualr.oyster.utilities.Scan;
import edu.ualr.oyster.utilities.SmithWaterman;
import edu.ualr.oyster.utilities.Sorensen;
import edu.ualr.oyster.utilities.Soundex;
import edu.ualr.oyster.utilities.Tanimoto;
import edu.ualr.oyster.utilities.TverskyIndex;
import java.util.Locale;

/**
 * Match Codes
 * True/False Matchcodes - these either match "equivalently" or they don't
 * 1. TRANSPOSE – a source and target are equivalent if there have at most one 
 * adjacent char that are swapped. i.e. John ≈ Jonh.<b>
 *  
 * 2. INITIAL – a source and target are equivalent if the target is an initial 
 * and it matches the first character of the source, i.e. J ≈ John.<b>
 *  
 * 3. NICKNAME – a source and target are equivalent if the source and target can
 * be found in the lookup table, i.e. Robert ≈ Bob.<b>
 *  
 * 4. SOUNDEX – a source and target are equivalent if the source and target 
 * produce the same hashing code according to the Soundex algorithm.<b>
 *  
 * 5. DMSOUNDEX  – a source and target are equivalent if the source and target 
 * produce the same hashing code according to the Daitch-Mokotoff Soundex 
 * algorithm, i.e. Moskowitz ≈ Moskovitz because they both produce the same code
 * 645740. Daitch-Mokotoff Soundex works very well on Jewish and Eastern 
 * European sounding names. So for areas that have a large population of Jewish 
 * or Eastern European person/descendents I would use this Soundex. See 
 * http://en.wikipedia.org/wiki/Daitch%E2%80%93Mokotoff_Soundex for more 
 * information.<b>
 *  
 * 6. IBMALPHACODE  – a source and target are equivalent if the source and 
 * target produce the same hashing code according to the IBM Alpha Code 
 * algorithm, i.e. Rodgers ≈ Rogers because they both produce the same code 
 * 04740000000000. See "An Overview of the Issues Related to the use of Personal
 * Identifiers", by Mark Armstrong for more information.<b>
 *  
 * 7. New York State Identification and Intelligence System (NYSIIS) – a source 
 * and target are equivalent if the source and target produce the same hashing 
 * code according to the NYSIIS Code algorithm, i.e. McKee = Mackie because they
 * both produce the same code MCY. This was the New York States attempt to 
 * improve on both Daitch-Mokotoff Soundex and regular Soundex  algorithm when 
 * used on ethic based names. See 
 * http://en.wikipedia.org/wiki/New_York_State_Identification_and_Intelligence_System
 * and "Name Search Techniques", Taft, R. L. (1970) for more information.<b>
 *  
 * 8. MATCHRATING  – a source and target are equivalent if the source and target
 * produce the similar hashing code that is then compared by a similarity 
 * algorithm according to the Western Airlines Match Rating Approach algorithm, 
 * i.e. Byrne produces BYRN and Boern produces BRN which both produce a 
 * similarity rating of 5. See http://en.wikipedia.org/wiki/Match_Rating_Approach
 * and "An Overview of the Issues Related to the use of Personal Identifiers" by
 * Mark Armstrong for more information.<b>
 * 
 * 9. Caverphone – a source and target are equivalent if the source and target 
 * produce the same hashing code according to the Caverphone algorithm.<b>
 * 
 * 9. Caverphone 2.0 – a source and target are equivalent if the source and 
 * target produce the same hashing code according to the Caverphone 2.0
 * algorithm.<b>
 * 
 * 10. Metaphone – a source and target are equivalent if the source and target 
 * produce the same hashing code according to the Metaphone algorithm.<b>
 *  <b>
 *  <b>
 *  <b>
 * Functionalized – these must met some threshold to be considered a match
 * 1. Levenshtein Edit Distance (LED) – default is 0.8 if LED match is used, 
 * signature for user defined threshold id LED(threshold), i.e.<b>
 * &lt;Rule Ident="FledLDS"&gt;
 *     &lt;Term Item="StudentFirstName" MatchResult="LED(0.8)"/&gt;
 *     &lt;Term Item="StudentLastName" MatchResult="Exact_Ignore_Case"/&gt;
 *     &lt;Term Item="StudentDateOfBirth" MatchResult="Exact"/&gt;
 *     &lt;Term Item="StudentSSN" MatchResult="Exact"/&gt;
 * &lt;/Rule&gt;
 * <b>
 * For more info see http://en.wikipedia.org/wiki/Levenshtein_distance. <b>
 *  
 * 2. Q-Gram Tetrahedral Ratio (QTR) – default is 0.25 if QTR match is used, 
 * signature for user defined threshold id QTR(threshold). For Example: <b>
 * &lt;Rule Ident="qF+LDS"&gt;
 *     &lt;Term Item="StudentFullName" MatchResult="QTR(0.05)"/&gt;
 *     &lt;Term Item="StudentDateOfBirth" MatchResult="Exact"/&gt;
 *     &lt;Term Item="StudentSSN" MatchResult="Exact"/&gt;
 * &lt;/Rule&gt;
 * <b>
 * For more information see http://www.gregholland.com/greg/academics.asp. <b>
 *  
 * 3. These all come under the heading of substring, Substring Left (Prefix) 
 * Substring Right (Suffix), and Substring Middle. I am also thinking about 
 * adding Subsequences, Border and Proper Substring.<b>
 * <ul>
 * <li>· SUBSTRLEFT(length) – a source and target are equivalent if the first x 
 * characters starting from the left are the same, i.e. SubStrLeft(4) makes 
 * MaryAnne ≈ Mary.</li>
 * <li>· SUBSTRRIGHT(length) – a source and target are equivalent if the last x 
 * characters starting from the right are the same, i.e SubStrRight(4) makes 
 * MaryAnne ≈ Anne.</li>
 * <li>· SUBSTRMID(start, length) – a source and target are equivalent if the if
 * the middle characters start from position x for a length of l are the same, 
 * SubStrMid(2,6) makes Krystal ≈ Crystalline.</li>
 * </ul><b>
 * For Example: <b>
 * &lt;Rule Ident="F5L5DS"&gt;
 *     &lt;Term Item="StudentFirstName" MatchResult="SUBSTRLEFT(5)"/&gt;
 *     &lt;Term Item="StudentLastName" MatchResult="SUBSTRMID(2, 5)"/&gt;
 *     &lt;Term Item="StudentDateOfBirth" MatchResult="Exact"/&gt;
 *     &lt;Term Item="StudentSSN" MatchResult="Exact"/&gt;
 * &lt;/Rule&gt;
 * <b>
 * 4. Scan <b>
 *    Scan(Direction, CharType, Length, Casing, Order)
 *    &lt;Term Item="StudentSSN" MatchResult="Scan()"/&gt;
 * <b>
 * 5. Smith-Waterman
 *    SmithWaterman(Match, Mismatch, Gap, Threshold)
 * <b>
 * 6. Needleman–Wunsch
 *    NeedlemanWunsch(Match, Mismatch, Gap, Threshold)
 * <b>
 * 6. Jaccard
 *    Jaccard(Threshold)
 * <b>
 * 6. Tanimoto - Strings that have Tanimoto coefficient values > 0.85 are 
 *    generally considered similar to each other.
 *    Tanimoto(Threshold)
 * <b>
 * 6. Tversky
 *    Tversky(Threshold)
 *    Tversky(Threshold, Alpha, Beta)
 * <b>
 * 
 * 
 * 
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.4F246EF3-2B69-ED25-F5F1-1237467C1A05]
// </editor-fold> 
public class OysterCompareDefault extends OysterComparator {
    //==========================================================================
    //  Edit distances & Similarity Matches
    //==========================================================================
    /** Single Character Transpose Utility */
    private OysterUtilityTranspose transpose;
    
    /** Levenshtein Edit Distance */
    private OysterEditDistance editDist;
    
    /** Q-Gram Tetrahedral Ratio operator */
    private QGramTetrahedralRatio qGram;
    
    /** Jaccard Coefficient */
    private Jaccard jaccard;
    
    /** Sorensen Similarity */
    private Sorensen sorensen;
    
    /** Tanimoto coefficient */
    private Tanimoto tanimoto;
    
    /** Tversky Index */
    private TverskyIndex tversky;
    
    //==========================================================================
    //  Soundexs
    //==========================================================================
    /** Standard Soundex utility */
    private Soundex soundex;
    
    /** Daitch-Mokotoff Soundex operator */
    private DaitchMokotoffSoundex dmSoundex;
    
    /** IBM AlphaCode operator */
    private IBMAlphaCode alphaCode;
    
    /** Match Rating Approach operator */
    private MatchRatingApproach matchRating;
    
    /** New York State Identification and Intelligence System operator */
    private NYSIISCode nysiis;
    
    /** Caverphone 1.0 phonetic matching algorithm by David Hood */
    private Caverphone caverphone;
    
    /** Caverphone 2.0 phonetic matching algorithm by David Hood */
    private Caverphone2 caverphone2;
    
    /** Metaphone phonetic algorithm */
    private Metaphone metaphone;
    
    /** Double Metaphone phonetic algorithm */
    private DoubleMetaphone metaphone2;
    
    /** Metaphone3 phonetic algorithm */
//    Metaphone3 metaphone3;
    
    //==========================================================================
    //  Genetic Simalrity Matches
    //==========================================================================
    /**  */
//    private NeedlemanWunsch needlemanWunsch;
    
    /**  */
    private SmithWaterman smithWaterman;
    
    //==========================================================================
    //  Others
    //==========================================================================
    /** Scan Utility */
    private Scan scan;
    
    /** Sub String Matches */
    private CharacterSubstringMatches substr;
    
    /** Nickname/Alias lookup */
    private OysterNickNameTable nnTable;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.D4C8F28B-5411-E71A-048B-3814127D8C66]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>OysterCompareDefault</code>.
     */
    public OysterCompareDefault () {
        super();
        
        String [] arr = {"INITIAL","TRANSPOSE","LED","QTR","JACCARD","SORENSEN",
            "TANIMOTO","TVERSKY","SOUNDEX","DMSOUNDEX","IBMALPHACODE","MATCHRATING",
            "NYSIIS","CAVERPHONE","CAVERPHONE2","METAPHONE","METAPHONE2","NEEDLEMANWUNSCH",
            "SMITHWATERMAN","SCAN","SUBSTRLEFT","SUBSTRRIGHT","SUBSTRMID","PSUBSTR","NICKNAME"};
        for (int i = 0; i < arr.length; i++){
            matchCodes.add(arr[i]);
            matchCodes.add("~"+arr[i]);
        }
        
        transpose = new OysterUtilityTranspose();
	editDist = new OysterEditDistance();
        qGram = new QGramTetrahedralRatio();
        jaccard = new Jaccard();
        sorensen = new Sorensen();
        tanimoto = new Tanimoto();
        tversky = new TverskyIndex();
        
        soundex = new Soundex();
        dmSoundex = new DaitchMokotoffSoundex();
        alphaCode = new IBMAlphaCode();
        matchRating = new MatchRatingApproach();
        nysiis = new NYSIISCode();
        caverphone = new Caverphone();
        caverphone2 = new Caverphone2();
        metaphone = new Metaphone();
        metaphone2 = new DoubleMetaphone();
//        metaphone3 = new Metaphone3();
        
//        needlemanWunsch = new NeedlemanWunsch();
        smithWaterman = new SmithWaterman();
        
        nnTable = new OysterNickNameTable();
        substr = new CharacterSubstringMatches();
        scan = new Scan();
    }

    /**
     * This method checks if the Strings are a single character transposition, or
     * if the normalized edit distance score is less than 0.20, or neither
     * @param s source String
     * @param t target String
     * @param matchType the type of match to preform.
     * @return "Transpose", "Led80" or "X"
     */
    @Override
    public String getMatchCode (String s, String t, String matchType) {
        String result, tempMatchType = matchType, direction = "", charType = "",
                upperCase = "", order = "";
        int sLen = 0, tLen = 0, length = 0, start = 0;
        float qTRThreshold = 0.25f, ledThreshold = 0.8f;
        float match = 1f, mismatch = 0f, gap = 0f, alpha = 0f, beta = 0f;
        boolean not = false;
        
        // Check for NOT operator
        if (matchType.toUpperCase(Locale.US).startsWith("~")){
            matchType = matchType.substring(1);
            not = true;
        }
        
        if (s != null) {
            sLen = s.length();
        }
        
        if (t != null) {
            tLen = t.length();
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
            
            start = Integer.parseInt(temp[0]);
            length = Integer.parseInt(temp[1]);
            
            matchType = "SubStrMid";
        } else if (matchType.toUpperCase(Locale.US).startsWith("PSUBSTR(")){
            matchType = matchType.trim().substring(8, matchType.length()-1);
            
            length = Integer.parseInt(matchType);
            matchType = "PSubStr";
        } else if (matchType.toUpperCase(Locale.US).startsWith("QTR(")){
            matchType = matchType.trim().substring(4, matchType.length()-1);
            
            qTRThreshold = Float.parseFloat(matchType);
            matchType = "qTR";
        } else if (matchType.toUpperCase(Locale.US).startsWith("LED(")){
            matchType = matchType.trim().substring(4, matchType.length()-1);
            
            ledThreshold = Float.parseFloat(matchType);
            matchType = "LED";
        } else if (matchType.toUpperCase().startsWith("JACCARD(")){
            matchType = matchType.trim().substring(8, matchType.length()-1);
            
            ledThreshold = Float.parseFloat(matchType);
            matchType = "JACCARD";
        } else if (matchType.toUpperCase().startsWith("TANIMOTO(")){
            matchType = matchType.trim().substring(9, matchType.length()-1);
            
            ledThreshold = Float.parseFloat(matchType);
            matchType = "TANIMOTO";
        } else if (matchType.toUpperCase().startsWith("SORENSEN(")){
            matchType = matchType.trim().substring(9, matchType.length()-1);
            
            ledThreshold = Float.parseFloat(matchType);
            matchType = "SORENSEN";
        } else if (matchType.toUpperCase().startsWith("TVERSKY(")){
            matchType = matchType.trim().substring(8, matchType.length()-1);
            
            String [] temp = matchType.split(",");
            ledThreshold = Float.parseFloat(temp[0].trim());
            
            if (temp.length > 1){
                alpha = Float.parseFloat(temp[1].trim());
                beta  = Float.parseFloat(temp[2].trim());
            }
            matchType = "TVERSKY";
        } else if (matchType.toUpperCase(Locale.US).startsWith("NEEDLEMANWUNSCH(")){
            matchType = matchType.trim().substring(16, matchType.length()-1);
            
            // Match, Mismatch, Gap, Threshold
            String [] temp = matchType.split("[,]");
            
            match        = Float.parseFloat(temp[0].trim());
            mismatch     = Float.parseFloat(temp[1].trim());
            gap          = Float.parseFloat(temp[2].trim());
            ledThreshold = Float.parseFloat(temp[3].trim());
            
            matchType = "NeedlemanWunsch";
        } else if (matchType.toUpperCase(Locale.US).startsWith("SMITHWATERMAN(")){
            matchType = matchType.trim().substring(14, matchType.length()-1);
            
            // Match, Mismatch, Gap, Threshold
            String [] temp = matchType.split("[,]");
            
            match        = Float.parseFloat(temp[0].trim());
            mismatch     = Float.parseFloat(temp[1].trim());
            gap          = Float.parseFloat(temp[2].trim());
            ledThreshold = Float.parseFloat(temp[3].trim());
            matchType = "SmithWaterman";
        } else if (matchType.toUpperCase(Locale.US).startsWith("SCAN(")){
            matchType = matchType.trim().substring(5, matchType.length()-1);
            
            // Scan(LR, DIGIT, 9, KeepCase, L2HKeepDup)
            String [] temp = matchType.split("[,]");
            direction  = temp[0].trim();
            charType   = temp[1].trim();
            length     = Integer.parseInt(temp[2].trim());
            upperCase  = temp[3].trim();
            order      = temp[4].trim();
            
            matchType = "SCAN";
        }
        
        //======================================================================
        //======================================================================
        if (!not) {
            if (matchType.equalsIgnoreCase("Initial") && s.charAt(0) == t.charAt(0)
                    && ((sLen == 1 && tLen > 1) || (sLen > 1 && tLen == 1))) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("Transpose") && transpose.differByTranspose(s, t)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("Soundex") && soundex.compareSoundex(s, t)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("DMSoundex") && dmSoundex.compareDMSoundex(s, t)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("IBMAlphaCode") && alphaCode.compareAlphaCodes(s, t)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("MatchRating") && matchRating.compareMatchRatingCodes(s, t)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("NYSIIS") && nysiis.compareNYSIISCodes(s, t)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("CAVERPHONE") && caverphone.compareCaverphone(s, t)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("CAVERPHONE2") && caverphone2.compareCaverphone(s, t)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("METAPHONE") && metaphone.compareMetaphone(s, t)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("METAPHONE2") && metaphone2.compareDoubleMetaphone(s, t)) {
            result = tempMatchType;
        }/* 
        else if (matchType.equalsIgnoreCase("METAPHONE3") && metaphone3.compareNYSIISCodes(s, t)) {
            result = tempMatchType;
        }*/ else if (matchType.equalsIgnoreCase("LED")){
            // calculate edit distance
            editDist.computeDistance(s, t);
            
            // if greater than or equal to normalized score it's a match
            if (editDist.computeNormalizedScore() >= ledThreshold) {
            result = tempMatchType;
            } else {
                result = "X";
            }
        } else if (matchType.equalsIgnoreCase("qTR") && qGram.qTR(s, t) >= qTRThreshold) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("JACCARD") && jaccard.computeDistance(s, t) >= ledThreshold) {
            // calculate Jaccard Coefficient
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("SORENSEN") && sorensen.computeDistance(s, t) >= ledThreshold) {
            // calculate Sorensen Similarity
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("TANIMOTO") && tanimoto.computeDistance(s, t) >= ledThreshold) {
            // calculate Tanimoto Coefficient
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("TVERSKY")){
            if (alpha != 0.0){
                tversky.setAlpha(alpha);
                tversky.setBeta(beta);
            }
            
            // calculate Tversky Index
            if (tversky.computeDistance(s, t) >= ledThreshold) {
            result = tempMatchType;
            } else {
                result = "X";
            }
        }/*
        else if (matchType.equalsIgnoreCase("NeedlemanWunsch")) {
            // calculate distance
            needlemanWunsch.computeNeedlemanWunsch(s, t, match, mismatch, gap);
            
            // if greater than or equal to normalized score it's a match
            if (needlemanWunsch.computeNormalizedScore(match) >= ledThreshold) {
            result = tempMatchType;
            } else {
                result = "X";
        }
        } */ else if (matchType.equalsIgnoreCase("SmithWaterman")) {
            // calculate distance
            smithWaterman.computeSmithWaterman(s, t, match, mismatch, gap);
            
            // if greater than or equal to normalized score it's a match
            if (smithWaterman.computeNormalizedScore() >= ledThreshold) {
                result = tempMatchType;
            } else {
                result = "X";
            }
        } else if (matchType.equalsIgnoreCase("NickName") && nnTable.isNicknamePair(s, t)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("SubStrLeft") && substr.left(s, t, length)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("SubStrRight") && substr.right(s, t, length)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("SubStrMid") && substr.mid(s, t, start, length)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("PSubStr") && substr.properSubString(s, t, length)) {
            result = tempMatchType;
        } else if (matchType.equalsIgnoreCase("SCAN") && scan.compareScan(s, t, direction, charType, length, upperCase, order)){
            result = tempMatchType;
        } else {
            result = "X";
        }
        } else {
            if (matchType.equalsIgnoreCase("Initial") && !(s.charAt(0) == t.charAt(0)
                    && ((sLen == 1 && tLen > 1) || (sLen > 1 && tLen == 1)))) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("Transpose") && !transpose.differByTranspose(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("qTR") && !(qGram.qTR(s, t) >= qTRThreshold)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("Soundex") && !soundex.compareSoundex(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("DMSoundex") && !dmSoundex.compareDMSoundex(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("IBMAlphaCode") && !alphaCode.compareAlphaCodes(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("MatchRating") && !matchRating.compareMatchRatingCodes(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("NYSIIS") && !nysiis.compareNYSIISCodes(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("CAVERPHONE") && !caverphone.compareCaverphone(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("CAVERPHONE2") && !caverphone2.compareCaverphone(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("METAPHONE") && !metaphone.compareMetaphone(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("METAPHONE2") && !metaphone2.compareDoubleMetaphone(s, t)) {
                result = tempMatchType;
            }/* 
             else if (matchType.equalsIgnoreCase("METAPHONE3") && !metaphone3.compareNYSIISCodes(s, t)) {
             result = tempMatchType;
             }*/ else if (matchType.equalsIgnoreCase("LED")) {
                // calculate edit distance
                editDist.computeDistance(s, t);

                // if greater than or equal to normalized score it's a match
                if (!(editDist.computeNormalizedScore() >= ledThreshold)) {
                    result = tempMatchType;
                } else {
                    result = "X";
                }
            } else if (matchType.equalsIgnoreCase("qTR") && !(qGram.qTR(s, t) >= qTRThreshold)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("JACCARD") && !(jaccard.computeDistance(s, t) >= ledThreshold)) {
                // calculate Jaccard Coefficient
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SORENSEN") && !(sorensen.computeDistance(s, t) >= ledThreshold)) {
                // calculate Sorensen Similarity
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("TANIMOTO") && !(tanimoto.computeDistance(s, t) >= ledThreshold)) {
                // calculate Tanimoto Coefficient
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("TVERSKY")) {
                if (alpha != 0.0) {
                    tversky.setAlpha(alpha);
                    tversky.setBeta(beta);
                }

                // calculate Tversky Index
                if (!(tversky.computeDistance(s, t) >= ledThreshold)) {
                    result = tempMatchType;
                } else {
                    result = "X";
                }
            }/*
             else if (matchType.equalsIgnoreCase("NeedlemanWunsch")) {
             // calculate distance
             needlemanWunsch.computeNeedlemanWunsch(s, t, match, mismatch, gap);
            
             // if greater than or equal to normalized score it's a match
             if (needlemanWunsch.computeNormalizedScore(match) >= ledThreshold) {
             result = tempMatchType;
             } else {
             result = "X";
             }
             } */ else if (matchType.equalsIgnoreCase("SmithWaterman")) {
                // calculate distance
                smithWaterman.computeSmithWaterman(s, t, match, mismatch, gap);

                // if greater than or equal to normalized score it's a match
                if (!(smithWaterman.computeNormalizedScore() >= ledThreshold)) {
                    result = tempMatchType;
                } else {
                    result = "X";
                }
            } else if (matchType.equalsIgnoreCase("NickName") && !nnTable.isNicknamePair(s, t)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrLeft") && !substr.left(s, t, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrRight") && !substr.right(s, t, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SubStrMid") && !substr.mid(s, t, start, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("PSubStr") && !substr.properSubString(s, t, length)) {
                result = tempMatchType;
            } else if (matchType.equalsIgnoreCase("SCAN") && !scan.compareScan(s, t, direction, charType, length, upperCase, order)) {
                result = tempMatchType;
            } else {
                result = "X";
            }
        }
        return result.toUpperCase();
    }
}

