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

package edu.ualr.oyster.io;

import edu.ualr.oyster.ErrorFormatter;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.sql.Types;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * OysterDatabaseWriter.java
 * Created on May 31, 2011 11:23:47 PM
 * @author enelso
 */
public class OysterDatabaseWriter {
    private Connection conn = null;
    private PreparedStatement pstmt = null;
    
    /** Used to determine what type of database is being connected to */
    private String connectionType = null;
    /** The server on which the database resides. This can be an IP address or
        Server name if a valid DSN entry exist */
    private String serverName = null;
    /** The port on which the database listens */
    private String portNumber = null;
    /** The name of the database */
    private String database = null;
    /** The name of the table or view that contains the data */
    private String tableName = null;
    /** The user's ID */
    private String userid = null;
    /** The user's Password*/
    private String password = null;
    
    boolean ODBC = false;
    
    long rows = 10000;
    String infile = null;
    boolean replace = true;
    
    /**
     * Creates a new instance of OysterDatabaseWriter
     */
    public OysterDatabaseWriter(){
    }
    
    /**
     * Creates a new instance of <code>OysterDatabaseWriter</code>.
     * @param tableName the database table name to be read.
     * @param connectionType the database connection type. The current supported
     * types are Oracle, MySQL, ODBC, and SQL server.
     * @param serverName the name of the server on which the database resides. 
     * This can be a DSN name or dotted decimal name.
     * @param portNumber the port on which the database listens.
     * @param database the name of the database.
     * @param userid the user id if applicable.
     * @param password the users password if applicable.
     */
    public OysterDatabaseWriter(String tableName, String connectionType, String serverName, String portNumber, String database, String userid, String password){
        this.connectionType = connectionType;
        this.serverName = serverName;
        this.tableName = tableName;
        this.portNumber = portNumber;
        this.database = database;
        this.userid = userid;
        this.password = password;
    }
    
    /**
     * Returns the <code>Connection</code> for this <code>OysterDatabaseWriter</code>.
     * @return the <code>Connection</code>.
     */
    public Connection getConn () {
        return conn;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.B5C04B79-C764-1D5E-B1D4-9B510D674F55]
    // </editor-fold> 
    /**
     * Sets the <code>Connection</code> for this <code>OysterDatabaseWriter</code>.
     * @param conn the <code>Connection</code> to be set.
     */
    public void setConn (Connection conn) {
        this.conn = conn;
    }

    /**
     * Returns the connection type for this <code>OysterDatabaseWriter</code>.
     * @return the connection type.
     */
    public String getConnectionType() {
        return connectionType;
    }

    /**
     * Sets the connection type for this <code>OysterDatabaseWriter</code>.
     * @param connectionType the connection type to be set.
     */
    public void setConnectionType(String connectionType) {
        this.connectionType = connectionType;
    }

    /**
     * Returns the server name for this <code>OysterDatabaseWriter</code>.
     * @return the server name.
     */
    public String getServerName() {
        return serverName;
    }

    /**
     * Sets the server name for this <code>OysterDatabaseWriter</code>.
     * @param serverName the server name to be set.
     */
    public void setServerName(String serverName) {
        this.serverName = serverName;
    }

    /**
     * Returns the port number for this <code>OysterDatabaseWriter</code>.
     * @return the port number.
     */
    public String getPortNumber() {
        return portNumber;
    }

    /**
     * Sets the port number for this <code>OysterDatabaseWriter</code>.
     * @param portNumber the port number to be set.
     */
    public void setPortNumber(String portNumber) {
        this.portNumber = portNumber;
    }

    /**
     * Returns the database name for this <code>OysterDatabaseWriter</code>.
     * @return the database name.
     */
    public String getDatabase() {
        return database;
    }

    /**
     * Sets the database name for this <code>OysterDatabaseWriter</code>.
     * @param database the database name to be set.
     */
    public void setDatabase(String database) {
        this.database = database;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.59CD3AAF-02B7-580D-58FE-96E5DE857818]
    // </editor-fold> 
    /**
     * Returns the table name for this <code>OysterDatabaseWriter</code>.
     * @return the table name.
     */
    public String getTableName () {
        return tableName;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.AD72E15F-E335-CA8C-43FB-2CAE4422AE4A]
    // </editor-fold> 
    /**
     * Sets the table name for this <code>OysterDatabaseWriter</code>.
     * @param tableName the table name to be set.
     */
    public void setTableName (String tableName) {
        this.tableName = tableName;
    }

    /**
     * Returns the userid for this <code>OysterDatabaseWriter</code>.
     * @return the userid.
     */
    public String getUserid() {
        return userid;
    }

    /**
     * Sets the userid for this <code>OysterDatabaseWriter</code>.
     * @param userid the userid to be set.
     */
    public void setUserid(String userid) {
        this.userid = userid;
    }

    /**
     * Returns the password for this <code>OysterDatabaseWriter</code>.
     * @return the password.
     */
    public String getPassword() {
        return password;
    }

    /**
     * Sets the password for this <code>OysterDatabaseWriter</code>.
     * @param password the password to be set.
     */
    public void setPassword(String password) {
        this.password = password;
    }
    
    /**
     * Returns whether the connection to the database is established.
     * @return true if the connection to the database is established, otherwise 
     * false.
     */
    public boolean isConnected(){
        String url;
        boolean flag = false;
        try{
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
        } catch(ClassNotFoundException ex){
            Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch(IllegalAccessException ex){
            Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch(InstantiationException ex){
            Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch(SQLException ex){
            Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        
        return flag;
    }
    
    public TreeMap<Long, Long> loadLink(HashMap<String, String> linkMap, HashMap<String, LinkedHashSet<String>> ruleMap){
        TreeMap<Long, Long> clusterDistribution = new TreeMap<Long, Long>();
        Map<String, Long> clusters = new LinkedHashMap<String, Long>();
        int counter = 0, rcCount = 0, rc;
        
        try {
            for (Iterator<Entry<String, String>> it = linkMap.entrySet().iterator(); it.hasNext();) {
                Entry<String, String> entry = it.next();
                String value = entry.getValue();
                LinkedHashSet<String> s = ruleMap.get(entry.getKey());

                long count = 0;
                if (clusters.containsKey(value)) {
                    count = clusters.get(value);
                }
                count++;
                clusters.put(value, count);
                
                rc = executeLinkTablePreparedStatement(entry.getKey(), value, s);
                
                if (rc > 0) {
                    rcCount += rc;
                    if ((counter + 1) % rows == 0) {
                        System.out.println((counter + 1) + "...");
                        conn.commit();
                    }
                    counter++;
                } else {
                    System.out.println("Did not insert record " + counter);
                }
            }
            
            conn.commit();
            
            System.out.println("Records read    " + counter);
            System.out.println("Records loaded  " + rcCount);

            for (Iterator<String> it = clusters.keySet().iterator(); it.hasNext();) {
                String key = it.next();
                long value = clusters.get(key);

                long count = 0;
                if (clusterDistribution.containsKey(value)) {
                    count = clusterDistribution.get(value);
                }
                count++;
                clusterDistribution.put(value, count);
            }
        } catch (SQLException ex) {
            Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return clusterDistribution;
    }
    
    //**************************************************************************
    //  ... Database Methods
    //**************************************************************************
    // FIXME: see http://findbugs.sourceforge.net/bugDescriptions.html#OBL_UNSATISFIED_OBLIGATION
    public void deleteData() {
        int rc;
        Statement stmt = null;
        try {
            stmt = conn.createStatement();
            rc = stmt.executeUpdate("delete from " + tableName);
            System.out.println("Records deleted\t" + rc);
        } catch (SQLException ex) {
            Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } finally {
            try {
                if (stmt != null) {
                    stmt.close();
                }
            } catch (SQLException ex) {
                Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
    }
    
    public boolean createLinkTable(){
        boolean flag = false;
        String sql;
        
        // checks on database and table names
        if (connectionType != null && connectionType.equalsIgnoreCase("oracle")) {
            sql = "CREATE TABLE " + database + "." + tableName + " (" +
                  "  source   varchar2(100) NOT NULL," +
                  "  refID    varchar2(100) NOT NULL," +
                  "  oysterID varchar2(100) NOT NULL," +
                  "  rules    varchar2(250) NULL," +
                  "  constraint PRIMARY KEY  (source, refID)," +
                  "  constraint KEY IDX_" + tableName + "_RefID (refID)" +
                  "  constraint KEY IDX_" + tableName + "_OysterID (oysterID)" +
                  ")";
        } else if (connectionType != null && connectionType.equalsIgnoreCase("mysql")) {
            sql = "CREATE TABLE `" + database + "`.`" + tableName + "` (" +
                  "  `source`   varchar(100) default NOT NULL," +
                  "  `refID`    varchar(100) default NOT NULL," +
                  "  `oysterID` varchar(100) default NOT NULL," +
                  "  `rules`    varchar(250) default NULL," +
                  "  PRIMARY KEY  (`source`, `refID`)," +
                  "  KEY `IDX_" + tableName + "_RefID` (`refID`)" +
                  "  KEY `IDX_" + tableName + "_OysterID` (`oysterID`)" +
                  ") ENGINE=MyISAM DEFAULT CHARSET=utf8";
        } else if (connectionType != null && connectionType.equalsIgnoreCase("sqlserver")) {
            sql = "CREATE TABLE [" + database + "].[dbo].[" + tableName + "] (" +
                  "  source   varchar(100) NOT NULL," +
                  "  refID    varchar(100) NOT NULL," +
                  "  oysterID varchar(100) NOT NULL," +
                  "  rules    varchar(250) NULL," +
                  "  constraint PRIMARY KEY  (source, refID)," +
                  "  constraint KEY [IDX_" + tableName + "_RefID] (refID)" +
                  "  constraint KEY [IDX_" + tableName + "_OysterID] (oysterID)" +
                  ")";
        } else if (connectionType != null && connectionType.equalsIgnoreCase("postgresql")) {
            sql = "CREATE TABLE " + database + "." + tableName + " (" +
                  "  source   varchar(100) NOT NULL," +
                  "  refID    varchar(100) NOT NULL," +
                  "  oysterID varchar(100) NOT NULL," +
                  "  rules    varchar(250) NULL," +
                  "  constraint PRIMARY KEY  (source, refID)," +
                  "  constraint KEY IDX_" + tableName + "_RefID (refID)" +
                  "  constraint KEY IDX_" + tableName + "_OysterID (oysterID)" +
                  ")";
        } else { // ODBC is the connection
            sql  = "";
        }

        Statement stmt = null;
        try{
            System.out.println("SQL: " + sql);
            stmt = conn.createStatement();
            stmt.executeUpdate(sql);
            System.out.println("Table [" + tableName + "] created.");
            flag = true;
        } catch (SQLException ex) {
            Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } finally {
            try {
                if (stmt != null) {
                    stmt.close();
                }
            } catch (SQLException ex) {
                Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
        return flag;
    }
    
    public boolean createLinkTable(Map<String, Integer> lengths){
        boolean flag = false;
        String sql;
        
        // checks on database and table names
        if (connectionType != null && connectionType.equalsIgnoreCase("oracle")) {
            sql = "CREATE TABLE " + database + "." + tableName + " (" +
                  "  source   varchar2(" + lengths.get("source") + ") NOT NULL," +
                  "  refID    varchar2(" + lengths.get("refID") + ") NOT NULL," +
                  "  oysterID varchar2(" + lengths.get("oysterID") + ") NOT NULL," +
                  "  rules    varchar2(" + lengths.get("rules") + ") NULL," +
                  "  constraint PRIMARY KEY  (source, refID)," +
                  "  constraint KEY IDX_" + tableName + "_RefID (refID)" +
                  "  constraint KEY IDX_" + tableName + "_OysterID (oysterID)" +
                  ")";
        } else if (connectionType != null && connectionType.equalsIgnoreCase("mysql")) {
            sql = "CREATE TABLE `" + database + "`.`" + tableName + "` (" +
                  "  `source`   varchar(" + lengths.get("source") + ") default NOT NULL," +
                  "  `refID`    varchar(" + lengths.get("refID") + ") default NOT NULL," +
                  "  `oysterID` varchar(" + lengths.get("oysterID") + ") default NOT NULL," +
                  "  `rules`    varchar(" + lengths.get("rules") + ") default NULL," +
                  "  PRIMARY KEY  (`source`, `refID`)," +
                  "  KEY `IDX_" + tableName + "_RefID` (`refID`)" +
                  "  KEY `IDX_" + tableName + "_OysterID` (`oysterID`)" +
                  ") ENGINE=MyISAM DEFAULT CHARSET=utf8";
        } else if (connectionType != null && connectionType.equalsIgnoreCase("sqlserver")) {
            sql = "CREATE TABLE [" + database + "].[dbo].[" + tableName + "] (" +
                  "  source   varchar(" + lengths.get("source") + ") NOT NULL," +
                  "  refID    varchar(" + lengths.get("refID") + ") NOT NULL," +
                  "  oysterID varchar(" + lengths.get("oysterID") + ") NOT NULL," +
                  "  rules    varchar(" + lengths.get("rules") + ") NULL," +
                  "  constraint PRIMARY KEY  (source, refID)," +
                  "  constraint KEY [IDX_" + tableName + "_RefID] (refID)" +
                  "  constraint KEY [IDX_" + tableName + "_OysterID] (oysterID)" +
                  ")";
        } else if (connectionType != null && connectionType.equalsIgnoreCase("postgresql")) {
            sql = "CREATE TABLE " + database + "." + tableName + " (" +
                  "  source   varchar(" + lengths.get("source") + ") NOT NULL," +
                  "  refID    varchar(" + lengths.get("refID") + ") NOT NULL," +
                  "  oysterID varchar(" + lengths.get("oysterID") + ") NOT NULL," +
                  "  rules    varchar(" + lengths.get("rules") + ") NULL," +
                  "  constraint PRIMARY KEY  (source, refID)," +
                  "  constraint KEY IDX_" + tableName + "_RefID (refID)" +
                  "  constraint KEY IDX_" + tableName + "_OysterID (oysterID)" +
                  ")";
        } else { // ODBC is the connection
            sql  = "";
        }

        Statement stmt = null;
        try{
            System.out.println("SQL: " + sql);
            stmt = conn.createStatement();
            stmt.executeUpdate(sql);
            System.out.println("Table [" + tableName + "] created.");
            flag = true;
        } catch (SQLException ex) {
            Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } finally {
            try {
                if (stmt != null) {
                    stmt.close();
                }
            } catch (SQLException ex) {
                Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
        return flag;
    }
    
    public boolean doesTableExist(){
        boolean flag = false;
        
        String sql = "";
        
        if (connectionType != null && connectionType.equalsIgnoreCase("oracle")) {
            sql = "SELECT COUNT(*) " +
                  "  FROM all_tables" +
                  " WHERE UPPER(table_name) = UPPER(" + tableName + ")";
        } else if (connectionType != null && connectionType.equalsIgnoreCase("mysql")) {
            sql = "SELECT COUNT(*)" +
                  "  FROM information_schema.tables" +
                  " WHERE table_schema = '" + database + "'" +
                  "   AND table_name = '" + tableName + "';";
        } else if (connectionType != null && connectionType.equalsIgnoreCase("sqlserver")) {
            sql = "SELECT COUNT(*) " +
                  "  FROM [" + database + "].sys.Tables" +
                  " WHERE name = [" + tableName + "]";
        } else if (connectionType != null && connectionType.equalsIgnoreCase("postgresql")) {
            sql = "SELECT COUNT(*)" +
                  "  FROM information_schema.tables" +
                  " WHERE table_name = '" + tableName + "'";
        } else { // ODBC is the connection
        }
        
        Statement stmt = null;
        ResultSet rs = null;
        try{
            stmt = conn.createStatement();
            rs = stmt.executeQuery(sql);
            
            if (rs.next()){
                int count = Integer.parseInt(rs.getString(1));
            
                if (count > 0) {
                    flag = true;
                }
            }
        } catch (SQLException ex) {
            Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } finally {
            try {
                if (stmt != null) {
                    stmt.close();
                }
                
                if (rs != null) {
                    rs.close();
                }
            } catch (SQLException ex) {
                Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
        return flag;
    }
    
    public void createLinkTablePreparedStatement(){
        String sql;
        try {
            // checks on database and table names
            if (connectionType != null && 
                    (connectionType.equalsIgnoreCase("oracle")) || connectionType.equalsIgnoreCase("postgresql")) {
            sql = "INSERT INTO "+ database + "." + tableName + "(source, refID, oysterID, rules) "+
                  "VALUES(?, ?, ?, ?)";
            } else if (connectionType != null && connectionType.equalsIgnoreCase("mysql")) {
            sql = "INSERT INTO `"+ database + "`.`" + tableName + "`(`source`, `refID`, `oysterID`, `rules`) "+
                  "VALUES(?, ?, ?, ?)";
            } else if (connectionType != null && connectionType.equalsIgnoreCase("sqlserver")) {
            sql = "INSERT INTO ["+ database + "].[dbo].[" + tableName + "](source, refID, oysterID, rules) "+
                  "VALUES(?, ?, ?, ?)";
            } else { // ODBC is the connection
            sql = "INSERT INTO "+ database + "." + tableName + "(source, refID, oysterID, rules) "+
                  "VALUES(?, ?, ?, ?)";
            }
            pstmt = conn.prepareStatement(sql);
        }
        catch (SQLException ex) {
            Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }
    
    public void createPreparedStatement(String [] arr){
        String sql = "INSERT INTO " + tableName + "(",
               values = "VALUES( ";
        try {
            for (int i = 0; i < arr.length; i++) {
                sql += arr[i] + ",";
                values += "?,";
            }
            
            // remove trailing comma
            sql = sql.substring(0, sql.length()-1) + ") ";
            sql += values.substring(0, values.length()-1) + ")";
            
            pstmt = conn.prepareStatement(sql);
        } catch (SQLException ex) {
            Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }

    private int executeLinkTablePreparedStatement(String key, String value, LinkedHashSet<String> s) {
        int rc = -1;
        try {
            rc = 0;
            
            String [] temp = key.split("[\\.]");
            
            if (!temp[0].equals("")) {
                pstmt.setString(1, temp[2]);
            } else {
                pstmt.setNull(1, Types.VARCHAR);
            }
            
            if (!temp[1].equals("")) {
                pstmt.setString(2, temp[1]);
            } else {
                pstmt.setNull(2, Types.VARCHAR);
            }
            
            if (!value.equals("")) {
                pstmt.setString(3, value);
            } else {
                pstmt.setNull(3, Types.VARCHAR);
            }
            
            if (s != null && s.size() > 0) {
                pstmt.setString(4, s.toString());
            } else {
                pstmt.setNull(4, Types.VARCHAR);
            }
            
            rc = pstmt.executeUpdate();
        } catch (SQLException ex) {
            Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        return rc;
    }

    public void close(){
        try {
            pstmt.close();
            conn.close();
        } catch (SQLException ex) {
            Logger.getLogger(OysterDatabaseWriter.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }
}
