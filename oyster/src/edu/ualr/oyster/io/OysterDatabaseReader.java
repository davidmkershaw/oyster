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

package edu.ualr.oyster.io;

import edu.ualr.oyster.ErrorFormatter;
import edu.ualr.oyster.core.ReferenceItem;
import edu.ualr.oyster.data.ClusterRecordSet;
import edu.ualr.oyster.data.CoDoSAOIR;
import edu.ualr.oyster.data.OysterIdentityRecord;
import edu.ualr.oyster.data.OysterIdentityRecordMap;
import edu.ualr.oyster.data.RecordTypes;
import java.sql.Connection; 
import java.sql.DriverManager;
import java.sql.ResultSet; 
import java.sql.SQLException;
import java.sql.Statement; 
import java.util.ArrayList;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * This class is used to read the Database files.
 * @author Eric D. Nelson
 */

// <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
// #[regen=yes,id=DCE.162F2A03-5070-032E-9498-F3DA00FE0F2C]
// </editor-fold> 
public class OysterDatabaseReader extends OysterSourceReader {

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.8E2A3F83-1AEA-58BB-2A1D-1AF07C4AC693]
    // </editor-fold> 
    /** The database connection */
    private Connection conn = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.B9F2104C-C101-D577-7C19-3030E68E6047]
    // </editor-fold> 
    /** The input reader */
    private Statement stmt = null;

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.1A6643D3-24A0-30D0-8CEA-0CDB8CE6858E]
    // </editor-fold> 
    /** */
    private ResultSet rs = null;

    /** Used to determine what type of database is being connected to */
    private String connectionType = null;

    /** The server on which the database resides. This can be an IP address or
        Server name if a valid DSN entry exist */
    private String serverName = null;
    
    /** The port on which the database listens */
    private String portNumber = null;
    
    /** The name of the database */
    private String database = null;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.6E19AD3B-0033-DA28-DAC1-DAE41C31F356]
    // </editor-fold> 
    /** The name of the table or view that contains the data */
    private String tableName = null;
    
    /** The user's ID */
    private String userid = null;
    
    /** The user's Password */
    private String password = null;
    
    /** The custom SQL string to run */
    private String overRideSQL = null;
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.50F48DA2-7022-DEB4-4D06-C90E4BDF2FC1]
    // </editor-fold> 
    /**
     * Creates a new instance of <code>OysterDatabaseReader</code>.
     */
    public OysterDatabaseReader (Logger log) {
        super(log);
    }

    /**
     * Creates a new instance of <code>OysterDatabaseReader</code>.
     * @param tableName the database table name to be read.
     * @param connectionType the database connection type. The current supported
     * types are Oracle, MySQL, ODBC, and SQL server.
     * @param serverName the name of the server on which the database resides. 
     * This can be a DSN name or dotted decimal name.
     * @param portNumber the port on which the database listens.
     * @param database the name of the database.
     * @param userid the user id if applicable.
     * @param password the users password if applicable.
     * @param ri the ArrayList of <code>ReferenceItems</code> that will be used to
     * store the parsed data.
     */
    public OysterDatabaseReader(String tableName, String connectionType, String serverName, String portNumber, String database, String userid, String password, ArrayList<ReferenceItem> ri, Logger log){
        super(log);
        
        this.connectionType = connectionType;
        this.serverName = serverName;
        this.tableName = tableName;
        this.portNumber = portNumber;
        this.database = database;
        this.userid = userid;
        this.password = password;
        
       setReferenceItems(ri);
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.0924D76D-CF3A-2EA8-9925-B90E57361D79]
    // </editor-fold> 
    /**
     * Returns the <code>Connection</code> for this <code>OysterDatabaseReader</code>.
     * @return the <code>Connection</code>.
     */
    public Connection getConn () {
        return conn;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.B5C04B79-C764-1D5E-B1D4-9B510D674F55]
    // </editor-fold> 
    /**
     * Sets the <code>Connection</code> for this <code>OysterDatabaseReader</code>.
     * @param conn the <code>Connection</code> to be set.
     */
    public void setConn (Connection conn) {
        this.conn = conn;
    }

    /**
     * Returns the connection type for this <code>OysterDatabaseReader</code>.
     * @return the connection type.
     */
    public String getConnectionType() {
        return connectionType;
    }

    /**
     * Sets the connection type for this <code>OysterDatabaseReader</code>.
     * @param connectionType the connection type to be set.
     */
    public void setConnectionType(String connectionType) {
        this.connectionType = connectionType;
    }

    /**
     * Returns the server name for this <code>OysterDatabaseReader</code>.
     * @return the server name.
     */
    public String getServerName() {
        return serverName;
    }

    /**
     * Sets the server name for this <code>OysterDatabaseReader</code>.
     * @param serverName the server name to be set.
     */
    public void setServerName(String serverName) {
        this.serverName = serverName;
    }

    /**
     * Returns the port number for this <code>OysterDatabaseReader</code>.
     * @return the port number.
     */
    public String getPortNumber() {
        return portNumber;
    }

    /**
     * Sets the port number for this <code>OysterDatabaseReader</code>.
     * @param portNumber the port number to be set.
     */
    public void setPortNumber(String portNumber) {
        this.portNumber = portNumber;
    }

    /**
     * Returns the database name for this <code>OysterDatabaseReader</code>.
     * @return the database name.
     */
    public String getDatabase() {
        return database;
    }

    /**
     * Sets the database name for this <code>OysterDatabaseReader</code>.
     * @param database the database name to be set.
     */
    public void setDatabase(String database) {
        this.database = database;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.59CD3AAF-02B7-580D-58FE-96E5DE857818]
    // </editor-fold> 
    /**
     * Returns the table name for this <code>OysterDatabaseReader</code>.
     * @return the table name.
     */
    public String getTableName () {
        return tableName;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,regenBody=yes,id=DCE.AD72E15F-E335-CA8C-43FB-2CAE4422AE4A]
    // </editor-fold> 
    /**
     * Sets the table name for this <code>OysterDatabaseReader</code>.
     * @param tableName the table name to be set.
     */
    public void setTableName (String tableName) {
        this.tableName = tableName;
    }

    /**
     * Returns the userid for this <code>OysterDatabaseReader</code>.
     * @return the userid.
     */
    public String getUserid() {
        return userid;
    }

    /**
     * Sets the userid for this <code>OysterDatabaseReader</code>.
     * @param userid the userid to be set.
     */
    public void setUserid(String userid) {
        this.userid = userid;
    }

    /**
     * Returns the password for this <code>OysterDatabaseReader</code>.
     * @return the password.
     */
    public String getPassword() {
        return password;
    }

    /**
     * Sets the password for this <code>OysterDatabaseReader</code>.
     * @param password the password to be set.
     */
    public void setPassword(String password) {
        this.password = password;
    }
    
    /**
     * Returns the overRideSQL for this <code>OysterDatabaseReader</code>.
     * @return the overRideSQL.
     */
    public String getOverRideSQL() {
        return overRideSQL;
    }

    /**
     * Sets the overRideSQL for this <code>OysterDatabaseReader</code>.
     * @param overRideSQL the overRideSQL to be set.
     */
    public void setOverRideSQL(String overRideSQL) {
        this.overRideSQL = overRideSQL;
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
                    url = "jdbc:mysql://" + serverName + ":" + portNumber + "/" + database + "?netTimeoutForStreamingResults=1200";
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
            Logger.getLogger(OysterDatabaseReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch(IllegalAccessException ex){
            Logger.getLogger(OysterDatabaseReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }  catch(InstantiationException ex){
            Logger.getLogger(OysterDatabaseReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        } catch(SQLException ex){
            Logger.getLogger(OysterDatabaseReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        
        return flag;
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.78D31DCE-0B36-FF5C-A347-E397E3C7485E]
    // </editor-fold> 
    /**
     * This method creates a select statement for the this datasource based on
     * the set reference items. If no reference items are set then a SELECT * is
     * created.
     * If the format type is of type date you will have to know what are the acceptable
     * format patterns for a particular database. Links are list below for each database.
     * <ul>
     * <li>MySQL - http://dev.mysql.com/doc/refman/5.1/en/date-and-time-functions.html#function_date-format</li>
     * <li>Oracle - http://download.oracle.com/docs/cd/B19306_01/server.102/b14200/sql_elements004.htm#i34510</li>
     * <li>PostGreSQL - http://www.postgresql.org/docs/8.1/interactive/functions-formatting.html</li>
     * <li>SQL Server - http://www.mssqltips.com/tip.asp?tip=1145</li>
     * </ul>
     * @return an SQL select statement for the current reference items.
     */
    private String createConnectionString () {
        String sql = "select ";
        
        // This is used to get around the java.io.EOFException: Can not read response from server. 
        // Expected to read X bytes, read N bytes before connection was unexpectedly lost.
        // See: http://forums.mysql.com/read.php?39,203407,217196#msg-217196
        if (connectionType.equalsIgnoreCase("MYSQL")) {
            sql += "SQL_NO_CACHE ";
        }
        
        if (getItemCount() == 0){
            sql += "*";
        } else {
            for (int i = 0; i < getItemCount(); i++) {
                ReferenceItem item = referenceItems.get(i);
                if(item.getFormat() != null){
                    if (item.getFormatType().equalsIgnoreCase("Date")){
                        if (connectionType.equalsIgnoreCase("ODBC")) {
                            sql += "Format(" + this.tableName + "." + item.getName() + ", '" + item.getFormat() + "') as " + item.getName() + ",";
                        } else if (connectionType.equalsIgnoreCase("ORACLE") || connectionType.equalsIgnoreCase("POSTGRESQL")) {
                            sql += "to_char(" + this.tableName + "." + item.getName() + ", '" + item.getFormat() + "') as " + item.getName() + ",";
                        } else if (connectionType.equalsIgnoreCase("MYSQL")) {
                            sql += "DATE_FORMAT(" + this.tableName + "." + item.getName() + ", '" + item.getFormat() + "') as " + item.getName() + ",";
                        } else if (connectionType.equalsIgnoreCase("SQLSERVER")) {
                            sql += "convert(varchar, " + this.tableName + "." + item.getName() + ", '" + item.getFormat() + "') as " + item.getName() + ",";
                        }
                    }
                } else {
                    sql += item.getName() + ", ";
                }
            }
            sql = sql.trim();

            // remove the trailing comma
            if (sql.endsWith(",")) {
                sql = sql.substring(0, sql.length() - 1);
            }
        }
        
        sql += " from " + this.tableName;
        
        return sql;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.FA284361-8B35-A3E4-1C7A-DE1BB01D90AC]
    // </editor-fold> 
    /**
     * This method initializes the SQL <code>Statement</code> and <code>ResultSet
     * </code> primes the data reader.
     */
    @Override
    public void open () {
//        ReferenceItem item = null;
        
        String sql;
        
        if (overRideSQL == null) {
            sql = createConnectionString();
        } else {
            sql = overRideSQL;
        }
        
        // Output the SQL statement
        StringBuilder sb = new StringBuilder(250);
        sb.append("SQL: ").append(sql).append(System.getProperty("line.separator"));
        logger.severe(sb.toString());
        System.out.println(sb.toString());
        
        try {
            // this handles the fact that MySQL will attempt to read the entire
            // database in to memory BEFORE operating on the data. This forces it 
            // to read on read at a time.
            if (this.connectionType.equalsIgnoreCase("mysql")){
                
                stmt = conn.createStatement(java.sql.ResultSet.TYPE_FORWARD_ONLY, java.sql.ResultSet.CONCUR_READ_ONLY);
//                stmt.setFetchSize(Integer.MIN_VALUE);
                stmt.setFetchSize(1000);
                
                rs = stmt.executeQuery(sql);
            } else {
                stmt = conn.createStatement();
                rs = stmt.executeQuery(sql);
            }
            
            /*
            ResultSetMetaData rsmd = rs.getMetaData();
            
            for (int i = 1; i <= rsmd.getColumnCount(); i++){
                item = new ReferenceItem();
                item.setName(rsmd.getColumnName(i));
                referenceItems.add(item);
            }
            */ 
        } catch (SQLException ex) {
            System.err.println(sql);
            Logger.getLogger(OysterDatabaseReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
        
    }

    /**
     * This method flushes any buffers and closes the database connection.
     */
    @Override
    public void close(){
        try {
            if (stmt != null) {
                stmt.close();
            }
            
            if (!conn.isClosed()) {
                conn.close();
            }
        } catch (SQLException ex) {
            Logger.getLogger(OysterDatabaseReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
        }
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.06A5CF25-F587-56E3-1808-E3B99CD034A1]
    // </editor-fold> 
    /**
     * getNextReference() is an external method that reads a reference
     * from the Reference Source, parses the reference into individual items and
     * store the items in the string array itemList
     * @return the number of items it found, zero at EOF
     */
    @Override
    public int getNextReference () {
        int count = 0;
        
        try {
            // clear refererence items
            for (int i = 0; i < getItemCount(); i++) {
                ReferenceItem item = referenceItems.get(i);
                item.setData("");
            }
            
            if (rs.next()) {
                for (int i = 0; i < getItemCount(); i++) {
                    ReferenceItem item = referenceItems.get(i);
                    String token = rs.getString(item.getName());
                    
                    if (!item.getName().startsWith("@")){
                        // if there are multiple items with the same item name 
                        // concatenate if the items are different
                        if (item.getData() != null && !item.getData().equals("")){
                            if (item.getData().equalsIgnoreCase(token)){
                                continue;
                            } else {
                                item.setData(item.getData() + "|" + token);
                            }
                        } else{
                            item.setData(token);
                        }
                        
                        // TODO: Add flag that is set from XML script to enable/disable this derived input RefID
                        if (item.getAttribute().equals("@RefID")){ 
                            if (item.getData() != null && !item.getData().equals("")){
                            item.setData(source + "." + item.getData());
                        } else {
                                item.setData(source + ".D" + this.recordCount);
                            }
                        }
                        
                        // ignore any records that have a blank or null id
                        if (item.getAttribute().equals("@RefID") && (item.getData() == null || item.getData().equals(""))){
                            count = 0;
                            break;
                        }
                        count++;
                    }
                }
                
                OysterIdentityRecord oysterIdentityRecord;
                
                switch (recordType) {
                    case RecordTypes.CODOSA:
                        oysterIdentityRecord = new CoDoSAOIR();
                        break;
                    case RecordTypes.MAP:
                        oysterIdentityRecord = new OysterIdentityRecordMap();
                        break;
                    default:
                        oysterIdentityRecord = new OysterIdentityRecordMap();
                }

                
                oysterIdentityRecord.convertToOIR(referenceItems);
                if (clusterRecord == null) {
                    clusterRecord = new ClusterRecordSet(recordType);
                }
                
                clusterRecord.clear();
                clusterRecord.insertRecord(oysterIdentityRecord);
                
                if (recordCount % getCountPoint() == 0) {
                    System.out.println(recordCount + "...");
                }
                
                recordCount++;
            }
        } catch (SQLException ex) {
            Logger.getLogger(OysterDatabaseReader.class.getName()).log(Level.SEVERE, ErrorFormatter.format(ex), ex);
            Logger.getLogger(OysterDatabaseReader.class.getName()).log(Level.SEVERE, clusterRecord.toString());
        }
        
        return count;
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.9C041E9F-5566-3CAB-3367-4E6E910F0251]
    // </editor-fold> 
    @Override
    public String getRecordImage () {
        throw new UnsupportedOperationException("Not supported yet.");
    }
    
    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.C7E3752F-EC5C-65D2-9992-9FC628A31D8D]
    // </editor-fold> 
    /**
     * Returns a string representation of the current record with 0x07 field delimiter
     * @return the current record as a 0x07 delimited string
     */
    public String getRecordImageAsDelimitedString () {
        StringBuilder result = new StringBuilder(250);
        if (getItemCount() > 0){
            for (int i = 0; i < getItemCount(); i++){
                ReferenceItem item = referenceItems.get(i);
                result.append(item.getData()).append("\u0007");
            }
            
            result = result.delete(result.length()-1, result.length());
        }
        
        return result.toString();
    }

    // <editor-fold defaultstate="collapsed" desc=" UML Marker "> 
    // #[regen=yes,id=DCE.5F7D0047-0587-A7D1-DC6E-279256BF4E19]
    // </editor-fold> 
    /**
     * Returns the keyword value pairs of the current record. Each pair is delimited
     * by the bell (0x07) character
     * @return the current record as attribute/value pairs
     */
    public String getRecordImageAsKeyValuePair() {
        StringBuilder result = new StringBuilder(250);
        if (getItemCount() > 0){
            for (int i = 0; i < getItemCount(); i++){
                ReferenceItem item = referenceItems.get(i);
                result.append(item.getName()).append("=").append(item.getData()).append("\u0007");
            }
            
            result = result.delete(result.length()-1, result.length());
        }
        
        return result.toString();
    }
}

