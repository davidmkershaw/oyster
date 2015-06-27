/*
 * Copyright 2012 John Talburt, Eric Nelson
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

package edu.ualr.oyster.core;

import java.util.HashSet;
import java.util.Set;

/**
 * RecordTypes.java
 * Created on Sep 20, 2011 12:05:00 PM
 * @author Eric D. Nelson
 */
    public class OysterKeywords {
    
    public static Set<String> keywords = null;
    
    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword <code>REFID</code>.
    */
    public final static String REFID 		=  "@RefID";
    
    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword <code>SKIP</code>.
    */
    public final static String SKIP 		=  "@Skip";

    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword <code>RID</code>.
    */
    public final static String RID 		=  "@RID";
    
    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword <code>OID</code>.
    */
    public final static String OID 		=  "@OID";
    
    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword 
     * <code>ASSERT_REF_TO_REF</code>.
    */
    public final static String ASSERT_REF_TO_REF=  "@AssertRefToRef";

    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword 
     * <code>ASSERT_REF_TO_STR</code>.
    */
    public final static String ASSERT_REF_TO_STR=  "@AssertRefToStr";

    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword 
     * <code>ASSERT_STR_TO_STR</code>.
    */
    public final static String ASSERT_STR_TO_STR=  "@AssertStrToStr";

    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword 
     * <code>ASSERT_SPLIT_STR</code>.
    */
    public final static String ASSERT_SPLIT_STR =  "@AssertSplitStr";

    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword 
    * <code>RUNMODE_MERGE_PURGE</code>.
    */
    public final static String RUNMODE_MERGE_PURGE =  "MergePurge";
    
    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword 
    * <code>RUNMODE_RECORD_LINKAGE</code>.
    */
    public final static String RUNMODE_RECORD_LINKAGE =  "RecordLinkage";
    
    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword 
    * <code>RUNMODE_IDENT_CAPTURE</code>.
    */
    public final static String RUNMODE_IDENT_CAPTURE =  "IdentityCapture";
    
    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword 
    * <code>RUNMODE_IDENT_RESOLVE</code>.
    */
    public final static String RUNMODE_IDENT_RESOLVE =  "IdentityResolution";
    
    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword 
    * <code>RUNMODE_IDENT_UPDATE</code>.
    */
    public final static String RUNMODE_IDENT_UPDATE =  "IdentityUpdate";
    
    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword 
    * <code>RUNMODE_ASSERT_REF2REF</code>.
    */
    public final static String RUNMODE_ASSERT_REF2REF =  "AssertRefToRef";
    
    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword 
    * <code>RUNMODE_ASSERT_REF2STR</code>.
    */
    public final static String RUNMODE_ASSERT_REF2STR =  "AssertRefToStr";
    
    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword 
    * <code>RUNMODE_ASSERT_STR2STR</code>.
    */
    public final static String RUNMODE_ASSERT_STR2STR =  "AssertStrToStr";
    
    /**
    * <P>The constant in the Java programming language, sometimes referred
    * to as a type code, that identifies the Oyster Keyword 
    * <code>RUNMODE_ASSERT_SPLIT_STR</code>.
    */
    public final static String RUNMODE_ASSERT_SPLIT_STR =  "AssertSplitStr";
    
    /**
     * Creates a new instance of ERTypes
     */
    // Prevent instantiation
    private OysterKeywords(){
        keywords = new HashSet<String>();
    }
}
