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

package edu.ualr.oyster.core;

import java.util.ArrayList;
import java.util.Map;
import java.util.Set; 

/**
 * Interface to a text file (run file) that has a list of paths to reference 
 * sources to be resolved. Responsibilities:
 * <ul>
 * <li>Sequentially access the reference sources</li>
 * <li>Validation that reference sources exists and can be accessed</li>
 * </ul>
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.20F5C140-2D57-F719-51EF-2AED9F7AB293]
// </editor-fold> 
public class OysterRunScript {
    /** The RunScripts Internal name */
    private static String name = null;
    
    /** Explanation Flag */
    private static boolean explanation = false;
    
    /** Debug Flag */
    private static boolean debug = false;
    
    /** Attribute file location/path */
    private static String attributeLocation = null;
    
    /** Identity Input file location/path/table name */
    private static String identityInputLocation = null;
    
    /** Identity Input type (None|Text|Database) */
    private static String identityInputType = null;
    
    /** Identity Input database server name */
    private static String identityInputServer = null;
    
    /** Identity Input database port */
    private static String identityInputPort = null;
    
    /** Identity Input database SID */
    private static String identityInputSID = null;
    
    /** Identity Input database user id*/
    private static String identityInputUserID = null;
    
    /** Identity Input database password*/
    private static String identityInputPasswd = null;
    
    /** Identity Input database Connection Type*/
    private static String identityInputCType = null;
    
    /** Identity Output file loaction/path/table name */
    private static String identityOutputLocation = null;
    
    /** Identity Output type (None|Text|Database) */
    private static String identityOutputType = null;
    
    /** Identity Output database server name */
    private static String identityOutputServer = null;
    
    /** Identity Output database port */
    private static String identityOutputPort = null;
    
    /** Identity Output database SID */
    private static String identityOutputSID = null;
    
    /** Identity Output database user id */
    private static String identityOutputUserID = null;
    
    /** Identity Output database password */
    private static String identityOutputPasswd = null;

    /** Identity Output database connection type */
    private static String identityOutputCType = null;
    
    /** Trace Flag */
    private static boolean identityOutputTrace = false;
    
    /** Link Output file loaction/path/table name */
    private static String linkOutputLocation = null;
    
    /** Link Output type (None|Text|Database) */
    private static String linkOutputType = null;
    
    /** Link Output database server name */
    private static String linkOutputServer = null;
    
    /** Link Output database port */
    private static String linkOutputPort = null;
    
    /** Link Output database SID */
    private static String linkOutputSID = null;
    
    /** Link Output database user id */
    private static String linkOutputUserID = null;
    
    /** Link Output database password */
    private static String linkOutputPasswd = null;
    
    /** Link Output database connection type */
    private static String linkOutputCType = null;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.E9956382-51B0-A5FB-4FB3-C72733138333]
    // </editor-fold> 
    /** List of sources and their capture flags */
    private static Set<String> sources;

    /** Log file path */
    private static String logFile = null;
    
    /** Number of logs to round robin */
    private static int logFileNum = 10;
    
    /** Max size of each log file before the next one is started */
    private static int logFileSize = 100000;
    
    /** Oyster Engine type */
    private static String engineType;
    
    /** System stats flag */
    private static boolean systemStats = false;

    /** bypass filter flag */
    private static boolean bypassFilter = true;

    /** OysterID Hash Type */
    private static String securityHash = "MD5";
    
    private static Map<Integer, ArrayList<String>> lcrd = null;
    
    /** Oyster EntityMap Type */
    private static String entityMapType = null;
    
    /** EntityMap database server name */
    private static String entityMapServer = null;
    
    /** EntityMap database port */
    private static String entityMapPort = null;
    
    /** EntityMap database SID */
    private static String entityMapSID = null;
    
    /** EntityMap database user id */
    private static String entityMapUserID = null;
    
    /** EntityMap database password */
    private static String entityMapPasswd = null;
    
    /** EntityMap database connection type */
    private static String entityMapCType = null;
    
    /** Oyster Index PreLoad Indicator */
    private static boolean preLoad = false;
    
    /** Oyster Change Report Detail Indicator */
    private static boolean changeReportDetail = false;
    
    /** The Oyster Run Mode */
    private static String runMode = null;
    
    /** The Assertion Input Source */
    private static String assertionInputLocation = null;
    
    private static int gc = -1;
    
    private static int slidingWindow = 0;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.410246AE-0491-60F3-9C4A-935B2D801814]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>OysterRunScript</code>.
     */
    public OysterRunScript () {
        //sources = new TreeMap<Integer, String>();
    }

    /**
     * Gets the internal name of the RunScript
     * @return name
     */
    public String getName() {
        return name;
    }

    /**
     * Set the internal name of the RunScript
     * @param aName the name to be set.
     */
    public void setName(String aName) {
        name = aName;
    }
    
    /**
     * Returns whether the <code>OysterRunScript</code> is in explanation mode.
     * @return true if the <code>OysterRunScript</code> is in explanation mode, otherwise false.
     */
    public boolean isExplanation() {
        return explanation;
    }

    /**
     * Enables/disables explanation mode for the <code>OysterRunScript</code>.
     * @param aExplanation true to enable explanation mode, false to disable it.
     */
    public void setExplanation(boolean aExplanation) {
        explanation = aExplanation;
    }

    /**
     * Returns whether the <code>OysterRunScript</code> is in debug mode.
     * @return true if the <code>OysterRunScript</code> is in debug mode, otherwise false.
     */
    public boolean isDebug() {
        return debug;
    }

    /**
     * Enables/disables debug mode for the <code>OysterRunScript</code>.
     * @param aDebug true to enable debug mode, false to disable it.
     */
    public void setDebug(boolean aDebug) {
        debug = aDebug;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.6C702AA9-AB0E-1D2C-6CAE-FB4829BFF2B0]
    // </editor-fold> 
    /**
     * Returns the Attribute Location for this <code>OysterRunScript</code>.
     * @return the Attribute Location.
     */
    public String getAttributeLocation () {
        return attributeLocation;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.9165D55E-9C84-2A6B-E2FE-917C286F0A29]
    // </editor-fold> 
    /**
     * Sets the Attribute Location for this <code>OysterRunScript</code>.
     * @param aLocation the Attribute Location to be set.
     */
    public void setAttributeLocation (String aLocation) {
        attributeLocation = aLocation;
    }

    /**
     * Returns the Identity Input Location for this <code>OysterRunScript</code>.
     * @return the Identity Input Location.
     */
    public String getIdentityInputLocation() {
        return identityInputLocation;
    }

    /**
     * Sets the Identity Input Location for this <code>OysterRunScript</code>.
     * @param aIdentityInputLocation the Identity Input Location to be set.
     */
    public void setIdentityInputLocation(String aIdentityInputLocation) {
        identityInputLocation = aIdentityInputLocation;
    }

    /**
     * Returns the Identity Input Type for this <code>OysterRunScript</code>.
     * @return the Identity Input Type.
     */
    public String getIdentityInputType() {
        return identityInputType;
    }

    /**
     * Sets the Identity Input Type for this <code>OysterRunScript</code>.
     * @param aIdentityInputType the Identity Input Type to be set.
     */
    public void setIdentityInputType(String aIdentityInputType) {
        identityInputType = aIdentityInputType;
    }

    /**
     * Returns the Identity Input Server for this <code>OysterRunScript</code>.
     * @return the Identity Input Server.
     */
    public String getIdentityInputServer() {
        return identityInputServer;
    }

    /**
     * Sets the Identity Input Server for this <code>OysterRunScript</code>.
     * @param aIdentityInputServer the Identity Input Server to be set.
     */
    public void setIdentityInputServer(String aIdentityInputServer) {
        identityInputServer = aIdentityInputServer;
    }

    /**
     * Returns the Identity Input Port for this <code>OysterRunScript</code>.
     * @return the Identity Input Port.
     */
    public String getIdentityInputPort() {
        return identityInputPort;
    }

    /**
     * Sets the Identity Input Port for this <code>OysterRunScript</code>.
     * @param aIdentityInputPort the Identity Input Port to be set.
     */
    public void setIdentityInputPort(String aIdentityInputPort) {
        identityInputPort = aIdentityInputPort;
    }

    /**
     * Returns the Identity Input SID for this <code>OysterRunScript</code>.
     * @return the Identity Input SID.
     */
    public String getIdentityInputSID() {
        return identityInputSID;
    }

    /**
     * Sets the Identity Input SID for this <code>OysterRunScript</code>.
     * @param aIdentityInputSID the Identity Input SID to be set.
     */
    public void setIdentityInputSID(String aIdentityInputSID) {
        identityInputSID = aIdentityInputSID;
    }

    /**
     * Returns the Identity Input UserID for this <code>OysterRunScript</code>.
     * @return the Identity Input UserID.
     */
    public String getIdentityInputUserID() {
        return identityInputUserID;
    }

    /**
     * Sets the Identity Input UserID for this <code>OysterRunScript</code>.
     * @param aIdentityInputUserID the Identity Input UserID to be set.
     */
    public void setIdentityInputUserID(String aIdentityInputUserID) {
        identityInputUserID = aIdentityInputUserID;
    }

    /**
     * Returns the Identity Input Password for this <code>OysterRunScript</code>.
     * @return the Identity Input Password.
     */
    public String getIdentityInputPasswd() {
        return identityInputPasswd;
    }

    /**
     * Sets the Identity Input Password for this <code>OysterRunScript</code>.
     * @param aIdentityInputPasswd the Identity Input Password to be set.
     */
    public void setIdentityInputPasswd(String aIdentityInputPasswd) {
        identityInputPasswd = aIdentityInputPasswd;
    }

    /**
     * Returns the Identity Input Connection Type for this <code>OysterRunScript
     * </code>.
     * @return the Identity Input Connection Type.
     */
    public String getIdentityInputCType() {
        return identityInputCType;
    }

    /**
     * Sets the Identity Input Connection Type for this <code>OysterRunScript
     * </code>.
     * @param aIdentityInputCType the Identity Input Connection Type to be set.
     */
    public void setIdentityInputCType(String aIdentityInputCType) {
        identityInputCType = aIdentityInputCType;
    }
    
    /**
     * Returns the Identity Output Location for this <code>OysterRunScript</code>.
     * @return the Identity Output Location.
     */
    public String getIdentityOutputLocation() {
        return identityOutputLocation;
    }

    /**
     * Sets the Identity Output Location for this <code>OysterRunScript</code>.
     * @param aIdentityOutputLocation the Identity Output Location to be set.
     */
    public void setIdentityOutputLocation(String aIdentityOutputLocation) {
        identityOutputLocation = aIdentityOutputLocation;
    }

    /**
     * Returns the Identity Output Type for this <code>OysterRunScript</code>.
     * @return the Identity Output Type.
     */
    public String getIdentityOutputType() {
        return identityOutputType;
    }

    /**
     * Sets the Identity Output Type for this <code>OysterRunScript</code>.
     * @param aIdentityOutputType the Identity Output Type to be set.
     */
    public void setIdentityOutputType(String aIdentityOutputType) {
        identityOutputType = aIdentityOutputType;
    }

    /**
     * Returns the Identity Output Server for this <code>OysterRunScript</code>.
     * @return the Identity Output Server.
     */
    public String getIdentityOutputServer() {
        return identityOutputServer;
    }

    /**
     * Sets the Identity Output Server for this <code>OysterRunScript</code>.
     * @param aIdentityOutputServer the Identity Output Server to be set.
     */
    public void setIdentityOutputServer(String aIdentityOutputServer) {
        identityOutputServer = aIdentityOutputServer;
    }

    /**
     * Returns the Identity Output Port for this <code>OysterRunScript</code>.
     * @return the Identity Output Port.
     */
    public String getIdentityOutputPort() {
        return identityOutputPort;
    }

    /**
     * Sets the Identity Output Port for this <code>OysterRunScript</code>.
     * @param aIdentityOutputPort the Identity Output Port to be set.
     */
    public void setIdentityOutputPort(String aIdentityOutputPort) {
        identityOutputPort = aIdentityOutputPort;
    }

    /**
     * Returns the Identity Output SID for this <code>OysterRunScript</code>.
     * @return the Identity Output SID.
     */
    public String getIdentityOutputSID() {
        return identityOutputSID;
    }

    /**
     * Sets the Identity Output SID for this <code>OysterRunScript</code>.
     * @param aIdentityOutputSID the Identity Output SID to be set.
     */
    public void setIdentityOutputSID(String aIdentityOutputSID) {
        identityOutputSID = aIdentityOutputSID;
    }

    /**
     * Returns the Identity Output UserID for this <code>OysterRunScript</code>.
     * @return the Identity Output UserID.
     */
    public String getIdentityOutputUserID() {
        return identityOutputUserID;
    }

    /**
     * Sets the Identity Output UserID for this <code>OysterRunScript</code>.
     * @param aIdentityOutputUserID the Identity Output UserID to be set.
     */
    public void setIdentityOutputUserID(String aIdentityOutputUserID) {
        identityOutputUserID = aIdentityOutputUserID;
    }

    /**
     * Returns the Identity Output Password for this <code>OysterRunScript</code>.
     * @return the Identity Output Password.
     */
    public String getIdentityOutputPasswd() {
        return identityOutputPasswd;
    }

    /**
     * Sets the Identity Output Password for this <code>OysterRunScript</code>.
     * @param aIdentityOutputPasswd the Identity Output Password to be set.
     */
    public void setIdentityOutputPasswd(String aIdentityOutputPasswd) {
        identityOutputPasswd = aIdentityOutputPasswd;
    }

    /**
     * Returns the Identity Output Connection Type for this <code>OysterRunScript
     * </code>.
     * @return the Identity Output Connection Type.
     */
    public String getIdentityOutputCType() {
        return identityOutputCType;
    }

    /**
     * Sets the Identity Output Connection type for this <code>OysterRunScript
     * </code>.
     * @param aIdentityOutputCType the Identity Output Connection type to be set.
     */
    public void setIdentityOutputCType(String aIdentityOutputCType) {
        identityOutputCType = aIdentityOutputCType;
    }

    /**
     * Returns the Identity Output Trace option for this <code>OysterRunScript
     * </code>. True produces a trace otherwise false;
     * @return the Identity Output Trace.
     */
    public boolean isIdentityOutputTrace() {
        return identityOutputTrace;
    }

    /**
     * Sets the Identity Output Trace option for this <code>OysterRunScript
     * </code>. True produces a trace otherwise false;
     * @param aIdentityOutputTrace the Identity Output Trace to be set.
     */
    public void setIdentityOutputTrace(boolean aIdentityOutputTrace) {
        identityOutputTrace = aIdentityOutputTrace;
    }
    
    /**
     * Returns the Link Output Location for this <code>OysterRunScript</code>.
     * @return the Link Output Location.
     */
    public String getLinkOutputLocation() {
        return linkOutputLocation;
    }

    /**
     * Sets the Link Output Location for this <code>OysterRunScript</code>.
     * @param aLinkOutputLocation the Link Output Location to be set.
     */
    public void setLinkOutputLocation(String aLinkOutputLocation) {
        linkOutputLocation = aLinkOutputLocation;
    }

    /**
     * Returns the Link Output Type for this <code>OysterRunScript</code>.
     * @return the Link Output Type.
     */
    public String getLinkOutputType() {
        return linkOutputType;
    }

    /**
     * Sets the Link Output Type for this <code>OysterRunScript</code>.
     * @param aLinkOutputType the Link Output Type to be set.
     */
    public void setLinkOutputType(String aLinkOutputType) {
        linkOutputType = aLinkOutputType;
    }

    /**
     * Returns the Link Output Server for this <code>OysterRunScript</code>.
     * @return the Link Output Server.
     */
    public String getLinkOutputServer() {
        return linkOutputServer;
    }

    /**
     * Sets the Link Output Server for this <code>OysterRunScript</code>.
     * @param aLinkOutputServer the Link Output Server to be set.
     */
    public void setLinkOutputServer(String aLinkOutputServer) {
        linkOutputServer = aLinkOutputServer;
    }

    /**
     * Returns the Link Output Port for this <code>OysterRunScript</code>.
     * @return the Link Output Port.
     */
    public String getLinkOutputPort() {
        return linkOutputPort;
    }

    /**
     * Sets the Link Output Port for this <code>OysterRunScript</code>.
     * @param aLinkOutputPort the Link Output Port to be set.
     */
    public void setLinkOutputPort(String aLinkOutputPort) {
        linkOutputPort = aLinkOutputPort;
    }

    /**
     * Returns the Link Output SID for this <code>OysterRunScript</code>.
     * @return the Link Output SID.
     */
    public String getLinkOutputSID() {
        return linkOutputSID;
    }

    /**
     * Sets the Link Output SID for this <code>OysterRunScript</code>.
     * @param aLinkOutputSID the Link Output SID to be set.
     */
    public void setLinkOutputSID(String aLinkOutputSID) {
        linkOutputSID = aLinkOutputSID;
    }

    /**
     * Returns the Link Output UserID for this <code>OysterRunScript</code>.
     * @return the Link Output UserID.
     */
    public String getLinkOutputUserID() {
        return linkOutputUserID;
    }

    /**
     * Sets the Link Output UserID for this <code>OysterRunScript</code>.
     * @param aLinkOutputUserID the Link Output UserID to be set.
     */
    public void setLinkOutputUserID(String aLinkOutputUserID) {
        linkOutputUserID = aLinkOutputUserID;
    }

    /**
     * Returns the Link Output Password for this <code>OysterRunScript</code>.
     * @return the Link Output Password.
     */
    public String getLinkOutputPasswd() {
        return linkOutputPasswd;
    }

    /**
     * Sets the Link Output Password for this <code>OysterRunScript</code>.
     * @param aLinkOutputPasswd the Link Output Password to be set.
     */
    public void setLinkOutputPasswd(String aLinkOutputPasswd) {
        linkOutputPasswd = aLinkOutputPasswd;
    }

    /**
     * Returns the Link Output Connection Type for this <code>OysterRunScript</code>.
     * @return the Link Output Connection Type.
     */
    public String getLinkOutputCType() {
        return linkOutputCType;
    }

    /**
     * Sets the Link Output Connection Type for this <code>OysterRunScript</code>.
     * @param aLinkOutputCType the Link Output Connection Type to be set.
     */
    public void setLinkOutputCType(String aLinkOutputCType) {
        linkOutputCType = aLinkOutputCType;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.606773F8-97E1-DF22-8B75-5630231948E3]
    // </editor-fold> 
    /**
     * Returns the Sources for this <code>OysterRunScript</code>.
     * @return the Sources.
     */
    public Set<String> getSources () {
        return sources;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.0A4383BE-DE50-325D-4777-2C737FFBAC19]
    // </editor-fold> 
    /**
     * Sets the Sources for this <code>OysterRunScript</code>.
     * @param s the Sources to be set.
     */
    public void setSources (Set<String> s) {
        sources = s;
    } 
    
    /**
     * Returns the Log File Name for this <code>OysterRunScript</code>.
     * @return Log Filename
     */
    public String getLogFile() {
        return logFile;
    }

    /**
     * Sets the Log Filename for this <code>OysterRunScript</code>.
     * @param aLogFile the Log Filename to be set
     */
    public void setLogFile(String aLogFile) {
        logFile = aLogFile;
    }

    /**
     * Returns the number of Log Files for this <code>OysterRunScript</code>.
     * @return the number of Log Files
     */
    public int getLogFileNum() {
        return logFileNum;
    }

    /**
     * Sets the number of Log Files for this <code>OysterRunScript</code>.
     * @param aLogFileNum the number of log files to be set
     */
    public void setLogFileNum(int aLogFileNum) {
        logFileNum = aLogFileNum;
    }

    /**
     * Returns the size of each Log File for this <code>OysterRunScript</code>.
     * @return the size of each Log File
     */
    public int getLogFileSize() {
        return logFileSize;
    }

    /**
     * Sets the size of each Log File for this <code>OysterRunScript</code>.
     * @param aLogFileSize the size of each Log File to be set
     */
    public void setLogFileSize(int aLogFileSize) {
        logFileSize = aLogFileSize;
    }
    
    /**
     * Returns the Engine Type for this <code>OysterRunScript</code>.
     * @return the Engine Type
     */
    public String getEngineType() {
        return engineType;
    }

    /**
     * Sets the Engine Type for this <code>OysterRunScript</code>.
     * @param aEngineType the Engine Type to be set
     */
    public void setEngineType(String aEngineType) {
        engineType = aEngineType;
    }

    /**
     * Returns whether the SystemStats flag is set for this <code>OysterRunScript</code>.
     * @return true if the SystemStats flag is set, otherwise false
     */
    public boolean isSystemStats() {
        return systemStats;
    }

    /**
     * Sets the SystemStats flag for this <code>OysterRunScript</code>.
     * @param aSystemStats the SystemStats to be set
     */
    public void setSystemStats(boolean aSystemStats) {
        systemStats = aSystemStats;
    }

    /**
     * Returns whether the Bypass Filter flag is set for this <code>OysterRunScript</code>.
     * @return true if the Bypass Filter flag is set, otherwise false
     */
    public boolean isBypassFilter() {
        return bypassFilter;
    }

    /**
     * Sets the Bypass Filter flag for this <code>OysterRunScript</code>.
     * @param aBypassFilter the BypassFilter to be set
     */
    public void setBypassFilter(boolean aBypassFilter) {
        bypassFilter = aBypassFilter;
    }

    /**
     * Returns the Security Hash type for this <code>OysterRunScript</code>.
     * @return the Security Hash type
     */
    public String getSecurityHash() {
        return securityHash;
    }

    /**
     * Sets the Security Hash for this <code>OysterRunScript</code>.
     * @param aSecurityHash the Security Hash to be set
     */
    public void setSecurityHash(String aSecurityHash) {
        securityHash = aSecurityHash;
    }

    /**
     * Returns the Least Common Rule Denominator filter for this <code>OysterRunScript</code>.
     * @return the LCRD filter
     */
    public Map<Integer, ArrayList<String>> getLcrd() {
        return lcrd;
    }

    /**
     * Sets the Least Common Rule Denominator filter for this <code>OysterRunScript</code>.
     * @param aLcrd the LCRD filter to be set
     */
    public void setLcrd(Map<Integer, ArrayList<String>> aLcrd) {
        lcrd = aLcrd;
    }

    public String getEntityMapType() {
        return entityMapType;
    }

    public void setEntityMapType(String aEntityMapType) {
        entityMapType = aEntityMapType;
    }

    public String getEntityMapServer() {
        return entityMapServer;
    }

    public void setEntityMapServer(String aEntityMapServer) {
        entityMapServer = aEntityMapServer;
    }

    public String getEntityMapPort() {
        return entityMapPort;
    }

    public void setEntityMapPort(String aEntityMapPort) {
        entityMapPort = aEntityMapPort;
    }

    public String getEntityMapSID() {
        return entityMapSID;
    }

    public void setEntityMapSID(String aEntityMapSID) {
        entityMapSID = aEntityMapSID;
    }

    public String getEntityMapUserID() {
        return entityMapUserID;
    }

    public void setEntityMapUserID(String aEntityMapUserID) {
        entityMapUserID = aEntityMapUserID;
    }

    public String getEntityMapPasswd() {
        return entityMapPasswd;
    }

    public void setEntityMapPasswd(String aEntityMapPasswd) {
        entityMapPasswd = aEntityMapPasswd;
    }

    public String getEntityMapCType() {
        return entityMapCType;
    }

    public void setEntityMapCType(String aEntityMapCType) {
        entityMapCType = aEntityMapCType;
    }

    public boolean isPreLoad() {
        return preLoad;
    }

    public void setPreLoad(boolean aPreLoad) {
        preLoad = aPreLoad;
    }

    public boolean isChangeReportDetail() {
        return changeReportDetail;
    }

    public void setChangeReportDetail(boolean aChangeReportDetail) {
        changeReportDetail = aChangeReportDetail;
    }

    public String getRunMode() {
        return runMode;
    }

    public void setRunMode(String aRunMode) {
        runMode = aRunMode;
    }
    
    public String getAssertionInputLocation() {
        return assertionInputLocation;
    }

    public void setAssertionInputLocation(String aAssertionInputLocation) {
        assertionInputLocation = aAssertionInputLocation;
    }
    
    public int getGc() {
        return gc;
    }

    public void setGc(int aGc) {
        gc = aGc;
    }

    public int getSlidingWindow() {
        return slidingWindow;
    }

    public void setSlidingWindow(int aSlidingWindow) {
        slidingWindow = aSlidingWindow;
    }
    
    /*
    @Override
    public synchronized Object clone() {
        OysterRunScript ors = new OysterRunScript();
        ors.explanation = this.explanation;
        ors.debug = this.debug;
        ors.attributeLocation = this.attributeLocation;

        ors.identityInputLocation = this.identityInputLocation;
        ors.identityInputType = this.identityInputType;
        ors.identityInputServer = this.identityInputServer;
        ors.identityInputPort = this.identityInputPort;
        ors.identityInputSID = this.identityInputSID;
        ors.identityInputUserID = this.identityInputUserID;
        ors.identityInputPasswd = this.identityInputPasswd;

        ors.identityOutputLocation = this.identityOutputLocation;
        ors.identityOutputType = this.identityOutputType;
        ors.identityOutputServer = this.identityOutputServer;
        ors.identityOutputPort = this.identityOutputPort;
        ors.identityOutputSID = this.identityOutputSID;
        ors.identityOutputUserID = this.identityOutputUserID;
        ors.identityOutputPasswd = this.identityOutputPasswd;

        ors.linkOutputLocation = this.linkOutputLocation;
        ors.linkOutputType = this.linkOutputType;
        ors.linkOutputServer = this.linkOutputServer;
        ors.linkOutputPort = this.linkOutputPort;
        ors.linkOutputSID = this.linkOutputSID;
        ors.linkOutputUserID = this.linkOutputUserID;
        ors.linkOutputPasswd = this.linkOutputPasswd;
        return ors;
    }*/
}

