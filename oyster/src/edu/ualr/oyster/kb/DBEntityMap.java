/*
 * Copyright 2011 John Talburt, Eric Nelson
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
package edu.ualr.oyster.kb;

import edu.ualr.oyster.ErrorFormatter;
import edu.ualr.oyster.data.ClusterRecord;
import edu.ualr.oyster.data.ClusterRecordSet;
import edu.ualr.oyster.data.CoDoSAOIR;
import edu.ualr.oyster.data.OysterIdentityRecord;
import edu.ualr.oyster.data.OysterIdentityRecordMap;
import edu.ualr.oyster.data.RecordTypes;
import java.io.PrintWriter;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.sql.Types;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TimeZone;
import java.util.TreeSet;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * DBEntityMap.java
 * Created on Sep 9, 2011 11:22:05 PM
 * @author Eric D. Nelson
 */
public class DBEntityMap extends EntityMap {


    /** */
    private Connection conn = null;
    /** */
    private PreparedStatement dpstmtCluster = null;
    /** */
    private PreparedStatement dpstmtRecord = null;
    /** */
    private PreparedStatement ipstmtCluster = null;
    /** */
    private PreparedStatement ipstmtRecord = null;
    /** */
    private PreparedStatement spstmtCluster = null;
    /** */
    private PreparedStatement spstmtRecord = null;
    /** */
    private PreparedStatement upstmtCluster = null;
    /** */
    private PreparedStatement upstmtRecord = null;
    /** Used to determine what type of database is being connected to */
    private String connectionType = null;
    /** The server on which the database resides. This can be an IP address or
    Server name if a valid DSN entry exist */
    private String serverName = null;
    /** The port on which the database listens */
    private String portNumber = null;
    /** The name of the database */
    private String database = null;
    /** The user's ID */
    private String userid = null;
    /** The user's Password*/
    private String password = null;
    /** */
    private SimpleDateFormat sdf = null;

    private int hit = 0,   miss = 0,  nullMiss = 0,   nonNullMiss = 0,  total = 0,  select = 0,  inserts = 0,  insertCluster = 0,  insertRecord = 0,  updates = 0,  updateRecord = 0,  selectCluster = 0,  updateCluster = 0,  selectRecord = 0,  deleteCluster = 0,  deleteRecord = 0;
    private int ihit = 0, imiss = 0, inullMiss = 0,  inonNullMiss = 0, itotal = 0, iselect = 0, iinserts = 0, iinsertCluster = 0, iinsertRecord = 0, iupdates = 0, iupdateRecord = 0, iselectCluster = 0, iupdateCluster = 0, iselectRecord = 0, ideleteCluster = 0, ideleteRecord = 0;
    
    /**
     * Creates a new instance of DBEntityMap
     */
    @SuppressWarnings("unchecked")
    public DBEntityMap(Map data, int recordType) {
        super(data, recordType);
        
        String DATE_FORMAT = "yyyy-MM-dd";
        sdf = new java.text.SimpleDateFormat(DATE_FORMAT);
        sdf.setTimeZone(TimeZone.getDefault());
    }

    @SuppressWarnings("unchecked")
    public DBEntityMap(Map data, String connectionType, String serverName, String portNumber, String database, String userid, String password, int recordType) {
        super(data, recordType);

        this.connectionType = connectionType;
        this.serverName = serverName;
        this.portNumber = portNumber;
        this.database = database;
        this.userid = userid;
        this.password = password;
        
        String DATE_FORMAT = "yyyy-MM-dd";
        sdf = new java.text.SimpleDateFormat(DATE_FORMAT);
        sdf.setTimeZone(TimeZone.getDefault());
    }

    /**
     * Returns the <code>Connection</code> for this <code>DBEntityMap</code>.
     * @return the <code>Connection</code>.
     */
    public Connection getConn() {
        return conn;
    }

    /**
     * Sets the <code>Connection</code> for this <code>DBEntityMap</code>.
     * @param conn the <code>Connection</code> to be set.
     */
    public void setConn(Connection conn) {
        this.conn = conn;
    }

    /**
     * Returns the connection type for this <code>DBEntityMap</code>.
     * @return the connection type.
     */
    public String getConnectionType() {
        return connectionType;
    }

    /**
     * Sets the connection type for this <code>DBEntityMap</code>.
     * @param connectionType the connection type to be set.
     */
    public void setConnectionType(String connectionType) {
        this.connectionType = connectionType;
    }

    /**
     * Returns the server name for this <code>DBEntityMap</code>.
     * @return the server name.
     */
    public String getServerName() {
        return serverName;
    }

    /**
     * Sets the server name for this <code>DBEntityMap</code>.
     * @param serverName the server name to be set.
     */
    public void setServerName(String serverName) {
        this.serverName = serverName;
    }

    /**
     * Returns the port number for this <code>DBEntityMap</code>.
     * @return the port number.
     */
    public String getPortNumber() {
        return portNumber;
    }

    /**
     * Sets the port number for this <code>DBEntityMap</code>.
     * @param portNumber the port number to be set.
     */
    public void setPortNumber(String portNumber) {
        this.portNumber = portNumber;
    }

    /**
     * Returns the database name for this <code>DBEntityMap</code>.
     * @return the database name.
     */
    public String getDatabase() {
        return database;
    }

    /**
     * Sets the database name for this <code>DBEntityMap</code>.
     * @param database the database name to be set.
     */
    public void setDatabase(String database) {
        this.database = database;
    }

    /**
     * Returns the userid for this <code>DBEntityMap</code>.
     * @return the userid.
     */
    public String getUserid() {
        return userid;
    }

    /**
     * Sets the userid for this <code>DBEntityMap</code>.
     * @param userid the userid to be set.
     */
    public void setUserid(String userid) {
        this.userid = userid;
    }

    /**
     * Returns the password for this <code>DBEntityMap</code>.
     * @return the password.
     */
    public String getPassword() {
        return password;
    }

    /**
     * Sets the password for this <code>DBEntityMap</code>.
     * @param password the password to be set.
     */
    public void setPassword(String password) {
        this.password = password;
    }

    public String getDatabaseCallInfo() {
        String result = "Total: " + itotal + "\t" +
                        "Hits: " + ihit + "\t" +
                        "Misses: " + imiss + "\t" +
                        "NonNullMiss: " + inonNullMiss + "\t" +
                        "NullMiss: " + inullMiss + "\t" + 
                        "Selects: " + iselect + "\t" +
                        "DB Selects: " + this.iselect + "\t" +
                        "DB Select Clusters: " + this.iselectCluster + "\t" +
                        "DB Select Records: " + this.iselectRecord + "\t" +
                        "DB Inserts: " + this.iinserts + "\t" +
                        "DB Insert Clusters: " + this.iinsertCluster + "\t" +
                        "DB Insert Records: " + this.iinsertRecord + "\t" +
                        "DB Updates: " + this.iupdates + "\t" +
                        "DB Updates Clusters: " + this.iupdateCluster + "\t" +
                        "DB Updates Records: " + this.iupdateRecord + "\t" +
                        "DB Delete Clusters: " + this.ideleteCluster + "\t" +
                        "DB Delete Records: " + this.ideleteRecord;
        return result;
    }
    
    public void clearDatabaseCallInfo() {
        ihit = imiss = inullMiss = inonNullMiss = iselect = itotal = 0;
        iselect = iselectCluster = iselectRecord = iinserts = iinsertCluster = 0;
        iinsertRecord = iupdates = iupdateCluster = iupdateRecord = ideleteCluster = ideleteRecord = 0;

    }
    
    /**
     * This method returns the <code>ClusterRecord</code> for the associated
     * OysterID.
     * @param oysterID the index into the DBEntityMap.
     * @return the ClusterRecord if it exist, otherwise null
     */
    @Override
    public ClusterRecord getCluster(String oysterID) {
        ClusterRecord cr;

        if (data.containsKey(oysterID)) {
            cr = data.get(oysterID);
            hit++;
            ihit++;
        } else {
            // get the data from the DB and add it to the Map
            cr = selectCluster(oysterID);
            miss++;
            imiss++;

            if (cr != null) {
                data.put(cr.getOysterID(), cr);
                nonNullMiss++;
                inonNullMiss++;
            }
            else {
                nullMiss++;
                inullMiss++;
            }
        }
        total++;
        itotal++;
        return cr;
    }

    /**
     * Removes the Cluster indexed by the input OysterID from the <code>DBEntityMap
     * </code>.
     * @param oysterID the index into the DBEntityMap.
     */
    @Override
    public void removeCluster(String oysterID) {
        // remove from map
        data.remove(oysterID);

        // remove from the DB tables
        delete(oysterID);
    }

    /**
     * Returns the size of the <code>DBEntityMap</code>.
     * @return the number of clusters.
     */
    @Override
    public int getSize() {
        int i = -1;
        String sql = "select count(distinct oysterID) from " + database + ".Cluster";

        try {
            Statement stmt = conn.createStatement();
            ResultSet rs = stmt.executeQuery(sql);

            if (rs.next()) {
                i = Integer.parseInt(rs.getString(1));
            }
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return i;
    }
    
    /**
     * The method addes a new entry to the <code>DBEntityMap</code>.
     * @param cr <code>ClusterRecord</code> to be added.
     */
    @Override
    public void add(ClusterRecord cr) {
        data.put(cr.getOysterID(), cr);

        insert(cr);
    }

    /**
     * This method adds a new identity to the <code>DBEntityMap</code>.
     * @param oysterID system generated OysterID.
     * @param oir <code>OysterIdentityRecord</code> to be added.
     * @param runID the id for the current resolution run.
     * @param rules the rules that fired for the current oysterID.
     */
    @Override
    public void addIdentity(String oysterID, OysterIdentityRecord oir, String runID, Set<String> rules, boolean traceOn) {
        ClusterRecord cr = getCluster(oysterID);

        if (cr == null) {
            cr = new ClusterRecordSet(recordType);
        }

        if (traceOn){
            // add a self trace to this oir
            TraceRecord tr = new TraceRecord();
//            tr.setOid("*");
            tr.setOid(oysterID);
            tr.setRunID(runID);
            tr.setRule(rules);
            oir.setCurrTrace(tr);
        }
        cr.insertRecord(oir);
        cr.setOysterID(oysterID);

        add(cr);
    }

    /**
     * This method adds a new identity to the <code>DBEntityMap</code>.
     * @param oysterID system generated OysterID.
     * @param cr <code>ClusterRecord</code> to be added.
     * @param runID the id for the current resolution run. A null runId is used 
     *        to determine that this is an existing cluster being loaded from a 
     *        file.
     * @param rules the rules that fired for the current oysterID.
     */
    @Override
    public void addIdentity(String oysterID, ClusterRecord cr, String runID, Set<String> rules, boolean traceOn) {
        cr.setOysterID(oysterID);
        
        // add a self trace to this cluster if it is a new cluster
        if (traceOn && runID != null) {
            TraceRecord tr = new TraceRecord();
//            tr.setOid("*");
            tr.setOid(oysterID);
            tr.setRunID(runID);
            tr.setRule(rules);
            cr.getOysterIdentityRecord(0).setCurrTrace(tr);
        }
        add(cr);
    }

    public void delayAddIdentity(String oysterID, ClusterRecord cr, int cid) {
        try {
            cr.setOysterID(oysterID);
            ipstmtCluster.setString(1, cr.getOysterID());

            if (cr.getCreationDate() != null) {
                ipstmtCluster.setString(2, sdf.format(cr.getCreationDate()));
            } else {
                ipstmtCluster.setNull(2, Types.VARCHAR);
            }
//            ipstmtCluster.setString(3, cr.getClusterType());
            ipstmtCluster.setInt(4, cr.getSize());
            if (cr.isPersistant()) {
                ipstmtCluster.setString(5, "Y");
            } else {
                ipstmtCluster.setString(5, "N");
            }
            ipstmtCluster.executeUpdate();

            // then insert in to the Record table
            for (int i = 0; i < cr.getSize(); i++) {
                OysterIdentityRecord oir = cr.getOysterIdentityRecord(i);

                // does the record already exist?
                ipstmtRecord.setString(1, oir.get("@RefID"));
                ipstmtRecord.setInt(2, cid);
                if (this.recordType == RecordTypes.MAP) {
                    Map m = (Map) oir.getData();
                    ipstmtRecord.setString(3, m.toString());
                } else {
                    ipstmtRecord.setString(3, (String) oir.getData());
                }
                ipstmtRecord.executeUpdate();
            }
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }
    
    /**
     * This method takes the new <code>ClusterRecord</code> and merges it with
     * the old <code>ClusterRecord</code> then replaces the old <code>
     * ClusterRecord</code> in the <code>DBEntityMap</code> with the merged one.
     * This allows any new information to be kept with the old.
     * @param oysterID the index into the DBEntityMap.
     * @param cr <code>ClusterRecord</code> to be updated.
     * @param runID the id for the current resolution run.
     * @param rules the rules that fired for the current oysterID.
     */
    @Override
    public void updateIdentity(String oysterID, ClusterRecord cr, String runID, Set<String> rules, boolean trace) {
        // get the identity for this index
        ClusterRecord old = getCluster(oysterID);

        if (old != null) {
            // set the merged flag
/*
            TreeSet<String> ts = new TreeSet<String>();
            ts.add(old.getClusterType());
            ts.add(cr.getClusterType());
//            System.out.println(ts);
            
            if (ts.toString().equals("[N]"))
                cr.setClusterType("N");
            else if (ts.toString().equals("[N, U]") || ts.toString().equals("[M, N]") || ts.toString().equals("[N, X]"))
                cr.setClusterType("U");
            else if (ts.toString().equals("[U]") || ts.toString().equals("[M, U]") || ts.toString().equals("[U, X]") ||
                     ts.toString().equals("[M]") || ts.toString().equals("[M, X]") || ts.toString().equals("[X]"))
                cr.setClusterType("M");
*/
            // update any merges
            // FIXME: How should I handle multiple merges, i.e. old has merges and so does cr, so there are now three sets of merges
            Map<String,String> merges = cr.getMerges();
            merges.putAll(old.getMerges());
            
            if (merges == null){
                merges = new LinkedHashMap<String,String>();
            }
            
            merges.put(old.getOysterID(), old.getValuesByAttribute("@RefID"));
            cr.setMerges(merges);
            
            cr.merge(old, runID, rules, trace);
            old = null;
            cr.setOysterID(oysterID);
            update(cr);
        } else {
            cr.setOysterID(oysterID);
            add(cr);
        }
    }

    @Override
    public List<String> getKeys(String[] entities) {
        List<String> list = new ArrayList<String>(entities.length);
        String sql = "select distinct oysterID from " + database + ".Cluster";

        try {
            Statement stmt = conn.createStatement();
            ResultSet rs = stmt.executeQuery(sql);

            while (rs.next()) {
                String oysterID = rs.getString(1);
                list.add(oysterID);
            }
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        
        return list;
    }
    
    //==========================================================================
    //  ... Database Methods
    //==========================================================================
    /**
     * Returns whether the connection to the database is established.
     * @param keepPreviousDB true if the current tables are to be used, otherwise false.
     * @return true if the connection to the database is established, otherwise
     * false.
     */
    public boolean isConnected(boolean keepPreviousDB) {
        String url;
        boolean flag = false;
        try {
            if (conn == null) {
                // connect to database
                if (connectionType != null && connectionType.equalsIgnoreCase("oracle")) {
                    Class.forName("oracle.jdbc.driver.OracleDriver");
                    // default port number
                    if (portNumber == null || portNumber.equals("")) {
                        portNumber = "1521";
                    }
                    url = "jdbc:oracle:thin:@" + serverName + ":" + portNumber + ":" + database;
                } else if (connectionType != null && connectionType.equalsIgnoreCase("mysql")) {
                    Class.forName("com.mysql.jdbc.Driver").newInstance();
                    // default port number
                    if (portNumber == null || portNumber.equals("")) {
                        portNumber = "3306";
                    }
                    url = "jdbc:mysql://" + serverName + ":" + portNumber + "/" + database;
                } else if (connectionType != null && connectionType.equalsIgnoreCase("sqlserver")) {
                    Class.forName("com.microsoft.sqlserver.jdbc.SQLServerDriver");
                    // default port number
                    if (portNumber == null || portNumber.equals("")) {
                        portNumber = "1433";
                    }
                    url = "jdbc:sqlserver://" + serverName + "\\" + database + ":" + portNumber;
                } else if (connectionType != null && connectionType.equalsIgnoreCase("postgresql")) {
                    Class.forName("org.postgresql.Driver");
                    // default port number
                    if (portNumber == null || portNumber.equals("")) {
                        portNumber = "5432";
                    }
                    url = "jdbc:postgresql://" + serverName + ":" + portNumber + "/" + database;
                } else { // ODBC is the default connection
                    Class.forName("sun.jdbc.odbc.JdbcOdbcDriver");
                    url = "jdbc:odbc:" + database;
                }

                if (userid != null && password != null) {
                    conn = DriverManager.getConnection(url, userid, password);
                } else {
                    conn = DriverManager.getConnection(url);
                }

                System.out.println("Connection: " + conn);
            }
            flag = !conn.isClosed();

            if (flag) {
                createPreparedStatements();
                
                if(!keepPreviousDB){
                    dropTables();
                    createTables();
                } else {
                    // do the tables exist
                    if (!doTablesExist()){
                        createTables();
                    }
                }
            }
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }

        return flag;
    }

    @Override
    public void close(){
        try {
            conn.close();
        } catch (SQLException ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        
        System.out.format("Total Cluster Requests : %1$,12d%n", this.total);
        System.out.format("Cache Hits             : %1$,12d  %2$,8.5f%n", this.hit, (float)this.hit / (float)this.total * 100);
        System.out.format("Cache Misses           : %1$,12d  %2$,8.5f%n", this.miss, (float)this.miss / (float)this.total * 100);
        System.out.format("Cache Non-Null Misses  : %1$,12d  %2$,8.5f%n", this.nonNullMiss, (float)this.nonNullMiss / (float)this.total * 100);
        System.out.format("Cache Null Misses      : %1$,12d  %2$,8.5f%n", this.nullMiss, (float)this.nullMiss / (float)this.total * 100);
        System.out.format("DB Selects             : %1$,12d%n", this.select);
        System.out.format("DB Select Clusters     : %1$,12d%n", this.selectCluster);
        System.out.format("DB Select Records      : %1$,12d%n", this.selectRecord);
        System.out.format("DB Inserts             : %1$,12d%n", this.inserts);
        System.out.format("   Clusters            : %1$,12d%n", this.insertCluster);
        System.out.format("   Records             : %1$,12d%n", this.insertRecord);
        System.out.format("DB Updates             : %1$,12d%n", this.updates);
        System.out.format("   Clusters            : %1$,12d%n", this.updateCluster);
        System.out.format("   Records             : %1$,12d%n", this.updateRecord);
        System.out.format("DB Delete Clusters     : %1$,12d%n", this.deleteCluster);
        System.out.format("DB Delete Records      : %1$,12d%n", this.deleteRecord);
        System.out.println();
    }
    
    private void createPreparedStatements() {
        String sql;

        try {
            sql = "delete from " + database + ".Cluster where `oysterID` = ?";
            dpstmtCluster = conn.prepareStatement(sql);

            sql = "delete from " + database + ".Record where `cid` = ?";
            dpstmtRecord = conn.prepareStatement(sql);

            sql = "insert into " + database + ".Cluster(`oysterID`,`creationDate`,`clusterType`,`size`,`persistant`) values (?,?,?,?,?)";
            ipstmtCluster = conn.prepareStatement(sql);

            sql = "insert into " + database + ".Record(`refID`,`cid`,`data`) values (?,?,?)";
            ipstmtRecord = conn.prepareStatement(sql);

            sql = "update " + database + ".Cluster set `oysterID` = ? where `cid` = ?";
            upstmtCluster = conn.prepareStatement(sql);

            sql = "update " + database + ".Record set `cid` = ? where `refID` = ?";
            upstmtRecord = conn.prepareStatement(sql);

            sql = "select * from " + database + ".Cluster where `oysterID` = ?";
            spstmtCluster = conn.prepareStatement(sql);

            sql = "select * from " + database + ".Record where `refID` = ?";
            spstmtRecord = conn.prepareStatement(sql);
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }

    private void createTables() {
        String sql = "";

        try {
            if (connectionType.equalsIgnoreCase("oracle")) {
            } else if (connectionType.equalsIgnoreCase("mysql")) {
                sql = "CREATE TABLE " + database + ".Cluster (\r\n" +
                        "   `cid`           INT(11) AUTO_INCREMENT NOT NULL,\r\n" +
                        "   `oysterID`     VARCHAR(20) NOT NULL,\r\n" +
                        "   `creationDate` VARCHAR(20),\r\n" +
                        "   `clusterType`  CHAR(1),\r\n" +
                        "   `size`         INT(11),\r\n" +
                        "   `persistant`   CHAR(1),\r\n" +
                        "  PRIMARY KEY (cid),\r\n" +
                        "  INDEX (oysterID)\r\n" +
                        ") ENGINE = MyISAM ROW_FORMAT = DEFAULT CHARACTER SET utf8 COLLATE utf8_general_ci;";
            } else if (connectionType.equalsIgnoreCase("sqlserver")) {
            } else {
            }

            System.out.println("SQL: " + sql);
            Statement stmt = conn.createStatement();
            stmt.executeUpdate(sql.toString());
            System.out.println("Table [" + database + ".Cluster] created.");
            System.out.println();

            if (connectionType.equalsIgnoreCase("oracle")) {
            } else if (connectionType.equalsIgnoreCase("mysql")) {
                sql = "CREATE TABLE " + database + ".Record (\r\n" +
                        "   `refID` VARCHAR(50) NOT NULL,\r\n" +
                        "   `cid`   INT NOT NULL,\r\n" +
                        "   `data`  LONGTEXT,\r\n" +
                        "  PRIMARY KEY (refID),\r\n" +
                        "  INDEX (cid)\r\n" +
                        ") ENGINE = MyISAM ROW_FORMAT = DEFAULT CHARACTER SET utf8 COLLATE utf8_general_ci;";
            } else if (connectionType.equalsIgnoreCase("sqlserver")) {
            } else {
            }

            System.out.println("SQL: " + sql);
            stmt.executeUpdate(sql.toString());
            System.out.println("Table [" + database + ".Record] created.");
            System.out.println();
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }

    private boolean doTablesExist() {
        boolean flag = false, clusterFlag = false, recordFlag = false;
        String sql;

        try {
            sql = "SELECT count(*) FROM `" + database + "`.`Cluster`";

            Statement stmt = conn.createStatement();
            ResultSet rs = stmt.executeQuery(sql);
            
            if (rs.next()){
                if (Integer.parseInt(rs.getString(1)) > 0)
                    clusterFlag = true;
            }
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }

        try {
            sql = "SELECT count(*) FROM `" + database + "`.`Record`";

            Statement stmt = conn.createStatement();
            ResultSet rs = stmt.executeQuery(sql);
            
            if (rs.next()){
                if (Integer.parseInt(rs.getString(1)) > 0)
                    recordFlag = true;
            }
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        
        if(clusterFlag && recordFlag)
            flag = true;
        
        return flag;
    }

    private void dropTables() {
        String sql;

        try {
            sql = "DROP TABLE `" + database + "`.`Cluster`";

            Statement stmt = conn.createStatement();
            stmt.executeUpdate(sql.toString());
            System.out.println("Table [" + database + ".Cluster] dropped.");
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }

        try {
            sql = "DROP TABLE `" + database + "`.`Record`";

            Statement stmt = conn.createStatement();
            stmt.executeUpdate(sql.toString());
            System.out.println("Table [" + database + ".Record] dropped.");
            System.out.println();
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }

    private void insert(ClusterRecord cr) {
        int rc;
        try {
            // insert into the Cluster table first
            // oysterID,creationDate,clusterType,size,persistant
            ipstmtCluster.setString(1, cr.getOysterID());

            if (cr.getCreationDate() != null) {
                ipstmtCluster.setString(2, sdf.format(cr.getCreationDate()));
            } else {
                ipstmtCluster.setNull(2, Types.VARCHAR);
            }
//            ipstmtCluster.setString(3, cr.getClusterType());
            ipstmtCluster.setInt(4, cr.getSize());
            if (cr.isPersistant()) {
                ipstmtCluster.setString(5, "Y");
            } else {
                ipstmtCluster.setString(5, "N");
            }
            rc = ipstmtCluster.executeUpdate();

            inserts += rc;
            iinserts+= rc;
            insertCluster += rc;
            iinsertCluster += rc;
            
            // then get the cid
            int cid = -1;
            spstmtCluster.setString(1, cr.getOysterID());
            ResultSet rs = spstmtCluster.executeQuery();
            if (rs.next()) {
                cid = rs.getInt("cid");
            }

            // then insert in to the Record table
            for (int i = 0; i < cr.getSize(); i++) {
                OysterIdentityRecord oir = cr.getOysterIdentityRecord(i);
                
                // does the record already exist?
                if (selectRecord(oir.get("@RefID")) != -1){
                    upstmtRecord.setInt(1, cid);
                    upstmtRecord.setString(2, oir.get("@RefID"));
                    
                    rc = upstmtRecord.executeUpdate();
                    
                    updates += rc;
                    iupdates += rc;
                    updateRecord += rc;
                    iupdateRecord += rc;
                }
                else {
                    // refID,cid,data
                    ipstmtRecord.setString(1, oir.get("@RefID"));
                    ipstmtRecord.setInt(2, cid);
                    if (this.recordType == RecordTypes.MAP){
                        Map m = (Map) oir.getData();
                        ipstmtRecord.setString(3, m.toString());
                    }
                    else ipstmtRecord.setString(3, (String) oir.getData());

                    rc = ipstmtRecord.executeUpdate();

                    inserts += rc;
                    iinserts += rc;
                    insertRecord += rc;
                    iinsertRecord += rc;
                }
            }
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }

    private void update(ClusterRecord cr) {
        int rc;
        try {
            // get the cid
            int cid = -1;
            spstmtCluster.setString(1, cr.getOysterID());
            ResultSet rs = spstmtCluster.executeQuery();
            if (rs.next()) {
                cid = rs.getInt("cid");
                selectCluster++;
                iselectCluster++;
            }

            // then update in to the Record table
            upstmtCluster.setString(1, cr.getOysterID());
            upstmtCluster.setInt(2, cid);

            rc = upstmtCluster.executeUpdate();
            
            updateCluster++;
            iupdateCluster++;
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }

    private void updateRecords(ClusterRecord cr) {
        try {
            // get the cid
            int cid = -1;
            spstmtCluster.setString(1, cr.getOysterID());
            ResultSet rs = spstmtCluster.executeQuery();
            if (rs.next()) {
                cid = rs.getInt("cid");
                selectCluster++;
                iselectCluster++;
            }

            // then update in to the Record table
            for (int i = 0; i < cr.getSize(); i++) {
                OysterIdentityRecord oir = cr.getOysterIdentityRecord(i);
                upstmtRecord.setInt(1, cid);
                upstmtRecord.setString(2, oir.get("@RefID"));

                upstmtRecord.executeUpdate();
                
                updateRecord++;
                iupdateRecord++;
            }
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }

    private ClusterRecord selectCluster(String oysterID) {
        ClusterRecord cr = null;
        int size = -1, cid;

        try {
            spstmtCluster.setString(1, oysterID);
            ResultSet rs = spstmtCluster.executeQuery();

            if (rs.next()) {
                cr = new ClusterRecordSet(recordType);
                cr.setOysterID(oysterID);
                
                cid = Integer.parseInt(rs.getString("cid"));

//                cr.setClusterType(rs.getString("clusterType"));
                size = Integer.parseInt(rs.getString("size"));

                String date = rs.getString("creationDate");
                if (date != null)
                    cr.setCreationDate(sdf.parse(date));
                else cr.setCreationDate(null);

                String persistant = rs.getString("persistant");
                if (persistant.equals("Y")) {
                    cr.setPersistant(true);
                } else {
                    cr.setPersistant(false);
                }

                select++;
                iselect++;
                spstmtRecord.setInt(1, cid);
                rs = spstmtRecord.executeQuery();
                while (rs.next()) {
                    OysterIdentityRecord oir;
                    
                    switch(this.recordType){
                        case RecordTypes.CODOSA:
                            oir = new CoDoSAOIR();
                            break;
                        case RecordTypes.MAP:
                            oir = new OysterIdentityRecordMap();
                            break;
                        default:
                            oir = new OysterIdentityRecordMap();
                    }
                    
                    oir.setData(rs.getString("data"));
                    cr.insertRecord(oir);
                    
                    select++;
                    iselect++;
                }
/*
                if (cr.getSize() != size) {
                    System.out.println("Error of DB export");
                    System.out.println("size    : " + size);
                    System.out.println("cr size : " + cr.getSize());
                    System.out.println(cr);
                }
*/
            }
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return cr;
    }

    private int selectRecord(String refID){
        int cid = -1;
        
        try {
            spstmtRecord.setString(1, refID);
            ResultSet rs = spstmtRecord.executeQuery();

            if (rs.next()) {
                cid = Integer.parseInt(rs.getString("cid"));
                selectRecord++;
                iselectRecord++;
            }
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        
        return cid;
    }
    
    private void delete(String oysterID) {
        int rc;
        try {
            // get the cid
            int cid = -1;
            spstmtCluster.setString(1, oysterID);
            ResultSet rs = spstmtCluster.executeQuery();
            if (rs.next()) {
                cid = rs.getInt("cid");
                selectCluster++;
                iselectCluster++;
            }
            
            dpstmtCluster.setString(1, oysterID);
            rc = dpstmtCluster.executeUpdate();
            deleteCluster += rc;
            ideleteCluster += rc;
            
            dpstmtRecord.setString(1, oysterID);
            rc = dpstmtRecord.executeUpdate();
            deleteRecord += rc;
            ideleteRecord += rc;
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }
    
    //==========================================================================
    //  ... Repository Methods
    //==========================================================================
    public void outputDB(PrintWriter out, String date){
        int count = 0, groups = 0;
        String sql = "SELECT c.cid, c.oysterID, c.creationDate, c.clusterType, c.size, c.persistant, r.data, r.refID " +
                     "FROM Cluster c INNER JOIN Record r ON r.cid = c.cid " +
                     "ORDER BY c.oysterID, r.refID";
        try{
            Statement stmt = conn.createStatement();
            ResultSet rs = stmt.executeQuery(sql);
            
            ClusterRecord cr = new ClusterRecordSet(this.recordType);
            OysterIdentityRecord oir;
            String prev = "", oysterID;
            while (rs.next()){
                oysterID = rs.getString("oysterID");

                if (!prev.equals(oysterID) && !prev.equals("")) {
                    out.println(cr.convertToXML(date));
                    cr = new ClusterRecordSet(this.recordType);
                    groups++;
                }
                cr.setOysterID(oysterID);
                
//                cr.setClusterType(rs.getString("clusterType"));
                
                String creationDate = rs.getString("creationDate");
                if (creationDate != null)
                    cr.setCreationDate(sdf.parse(date));
                else cr.setCreationDate(null);

                String persistant = rs.getString("persistant");
                if (persistant.equals("Y")) {
                    cr.setPersistant(true);
                } else {
                    cr.setPersistant(false);
                }
                
                switch (this.recordType) {
                    case RecordTypes.CODOSA:
                        oir = new CoDoSAOIR();
                        break;
                    case RecordTypes.MAP:
                        oir = new OysterIdentityRecordMap();
                        break;
                    default:
                        oir = new OysterIdentityRecordMap();
                }

                oir.setData(rs.getString("data"));
                cr.insertRecord(oir);
                
                prev = oysterID;
                count++;
            }
            
            // handle the last records
            out.println(cr.convertToXML(date));
            groups++;
            
            stmt.close();
            System.out.println("Clusters:\t" + groups);
            System.out.println("References:\t" + count);
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }
    
    public int getCounts(String clusterType){
        int count = 0;
        String sql = "SELECT count(*) " +
                     "FROM Cluster c  " +
                     "WHERE c.clusterType = '" + clusterType + "'";
        
        try{
            Statement stmt = conn.createStatement();
            ResultSet rs = stmt.executeQuery(sql);
            
            if (rs.next()){
                count = Integer.parseInt(rs.getString(1));
            }
        } catch (Exception ex) {
            Logger.getLogger(DBEntityMap.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return count;
    }
}
