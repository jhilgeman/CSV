/*
 * CSV Class
 * 
 * Author: Jonathan Hilgeman
 * Date: 2019-08-15
 * Version: 1.2
 *
 * Description:
 * The CSV class is intended to simplify the reading and parsing of CSV files for .NET
 * applications and add-ins, and handle some of the related tasks.
 * 
 * Features:
 * - Proper handling of quoted and multi-line values.
 * - Error-checking (e.g. missing quotes) and recovery.
 * - Fast performance on large CSV files (100,000 twenty-field records can be read in 2 seconds or less).
 * - Fast duplicate-checking using SHA-256 hashes of each record (optional, defaults to enabled).
 * - Support for different file encodings and multi-byte languages.
 * - Support for DOS, Mac, and *nix line endings.
 * - User-defineable delimiter, quote, and quote escape characters.
 * - Support for all key events, including progress updates every 1,000 records.
 * - Defaults to using a DataTable as the format for storage of parsed data.
 * - Extensible to allow user to define their own data storage.
 * - Separated storage for duplicate and bad records.
 * - Write function for saving parsed data back to a CSV (can be copied/repurposed for saving duplicate/bad records).
 * - Support for asynchronous reading (see TestForm for examples of how to handle cross-thread callbacks).
 * - Optional constructor to read from an existing data stream.
 * 
 * Version History:
 * 2014-05-21 :: 1.1 :: Added OptimizeDataTable() routine.
 * 2019-08-15 :: 1.2 :: Removed optimization, left it up to the user instead.
 * 
 * #######################################################################################
 * ## Example #1: Simple reading using all defaults 
 * #######################################################################################
 * 
 *   CSV csvFile = new CSV("C:\\sample.csv");
 *   DataTable parsedData = csvFile.ToDataTable();
 *   
 * #######################################################################################
 * 
 * 
 * #######################################################################################
 * ## Example #2: Parsing a CSV with headers but without dupe-checking 
 * #######################################################################################
 * 
 *   CSV csvFile = new CSV("C:\\sample.csv",true,false);
 *   DataTable parsedData = csvFile.ToDataTable();
 *   
 * #######################################################################################
 * 
 * 
 * #######################################################################################
 * ## Example #3: Asynchronous reading with custom event handlers 
 * #######################################################################################
 *
 *   // Example callback function for progress updates
 *   private void csvProgressCheck(object sender, CSV csvReader, List<string> lastRecord)
 *   {
 *      // Using "Invoke" in case we use async reading
 *      this.Invoke(new MethodInvoker(delegate
 *      {
 *         txtTotalCount.Text = csvReader.TotalRowCount.ToString();
 *         txtGoodCount.Text  = csvReader.GoodRowCount.ToString();
 *         txtBadCount.Text   = csvReader.BadRowCount.ToString();
 *         txtDupeCount.Text  = csvReader.DuplicateRowCount.ToString();
 *      }));
 *   }
 *
 *   CSV csvFile = new CSV("C:\\sample.csv",true,false);
 *   csvFile.onReadInterval += csvProgressCheck;
 *   DataTable parsedData = csvFile.ToDataTable(true);
 *   
 * #######################################################################################
 */

using System;
using System.Collections.Generic;
using System.Text;
using System.IO;
using System.Text.RegularExpressions;
using System.Threading;
using System.ComponentModel;
using System.Data;
using System.Security.Cryptography; // For SHA256 hashing
using System.Linq;

namespace MyUtilities
{
    public class CSV
    {
        // ######################################################################
        //  PROPERTIES
        // ######################################################################

        // Class version
        protected string version = "1.2";

        // Defines the name of the data - mostly cosmetic
        protected string dataName = "";

        // Characters for processing
        public char charDelimiter = ',';
        public char charQuote = '"';
        public char charEscapeQuote = '\\';

        // Validation results
        const int VALIDATION_OK = 0;
        const int VALIDATION_DUPLICATE = 1;
        const int VALIDATION_ERROR_WRONG_NUMBER_OF_FIELDS = 2;
        const int VALIDATION_ERROR_DUPLICATE_RECORD = 3;
        const int VALIDATION_ERROR_UNCLOSED_QUOTES = 4;
        const int VALIDATION_ERROR_OTHER = 5;

        // Counters (NOTE: onRecordRead event responsible for updating these counters)
        public int TotalRowCount { get; protected set; }
        public int GoodRowCount { get; protected set; }
        public int BadRowCount { get; protected set; }
        public int DuplicateRowCount { get; protected set; }

        // Container for error and duplicate records (useful for dumping them to a separate file for further analysis)
        public List<List<string>> errorRecords = null;
        public Dictionary<string, List<string>> duplicateRecords = null;

        // Streams and readers
        protected StreamReader reader = null;
        protected Stream dataStream = null;

        // Flags
        protected bool completed = false;
        protected bool hasHeaders = false;
        protected bool checkForDupes = false;

        // First record
        protected List<string> firstRecord = null;

        // Container for hashes
        protected HashSet<string> recordHashes = null;

        public int ReadInterval = 10000;

        public Encoding encoding;

        // ######################################################################
        //  CONSTRUCTORS
        // ######################################################################

        // Pass in a File
        public CSV(string csvFile, bool hasHeaders = true, bool checkForDupes = true, char charDelimiter = ',', char charQuote = '"', char charEscapeQuote = '\\', Encoding fileEncoding = null)
        {
            // Try to open the file as a stream
            if (File.Exists(csvFile))
            {
                this.dataStream = new FileStream(csvFile, FileMode.Open, FileAccess.Read, FileShare.Read);
                this.Initialize(csvFile, hasHeaders, checkForDupes, charDelimiter, charQuote, charEscapeQuote, fileEncoding);
            }
            else
            {
                throw new Exception(csvFile + " does not exist!");
            }
        }

        // Pass in a Stream
        public CSV(Stream dataStream, bool hasHeaders = true, bool checkForDupes = true, char charDelimiter = ',', char charQuote = '"', char charEscapeQuote = '\\', Encoding fileEncoding = null)
        {
            // Pass straight to Initialize() method
            this.dataStream = dataStream;
            this.Initialize("Stream", hasHeaders, checkForDupes, charDelimiter, charQuote, charEscapeQuote, fileEncoding);
        }

        // Common Initialization
        protected void Initialize(string dataName, bool hasHeaders = true, bool checkForDupes = true, char charDelimiter = ',', char charQuote = '"', char charEscapeQuote = '\\', Encoding fileEncoding = null)
        {
            // Set protected class properties
            this.charDelimiter = charDelimiter;
            this.charQuote = charQuote;
            this.charEscapeQuote = charEscapeQuote;
            this.hasHeaders = hasHeaders;
            this.checkForDupes = checkForDupes;
            this.dataName = dataName;

            // Start stream reader
            if (fileEncoding != null)
            {
                this.encoding = fileEncoding;
                this.reader = new StreamReader(this.dataStream, fileEncoding);
            }
            else
            {
                this.encoding = Encoding.UTF8;
                this.reader = new StreamReader(this.dataStream);
            }
            this.decoder = this.encoding.GetDecoder();

            // Cast int characters
            this.chrDelimiter = (int)this.charDelimiter;
            this.chrQuote = (int)this.charQuote;
            this.chrEscapeQuote = (int)this.charEscapeQuote;


            // Pull first record and reset stream
            this.firstRecord = this.ReadRecord();
            this.Reset();
        }

        // ######################################################################
        //  BASIC METHODS (READ ALL RECORDS, RESET, AND WRITE)
        // ######################################################################

        /// <summary>
        /// If a file has not been read yet, this simply reads all records from the file, 
        /// </summary>
        public void ReadAllRecords(bool runAsync = false)
        {
            if (!this.completed)
            {
                if (runAsync)
                {
                    // Run asynchronously
                    BackgroundWorker bw = new BackgroundWorker();
                    bw.WorkerReportsProgress = true;
                    bw.DoWork += new DoWorkEventHandler(bw_ReadAllRecords);
                    bw.RunWorkerAsync();
                }
                else
                {
                    // Run synchronously
                    bw_ReadAllRecords(this, new DoWorkEventArgs(null));
                }
            }
        }

        // Worker process for reading records
        protected void bw_ReadAllRecords(object sender, DoWorkEventArgs e)
        {
            // NOTE: Uncomment profiler lines to do performance testing
            // Profiler readTimer = new Profiler();

            // Skip first record if need be
            List<string> csvRecord = null;
            if (this.hasHeaders)
                csvRecord = this.ReadRecord();

            // Loop through entire stream
            while (this.reader.EndOfStream == false)
            {
                // Get record
                csvRecord = this.ReadRecord();

                // Skip blank records
                if (csvRecord.Count == 0)
                {
                    continue;
                }

                // Perform validation
                int validationResult = call_recordValidatorHandler(this, csvRecord);

                // Increment record counter
                this.TotalRowCount++;

                if ((this.TotalRowCount % ReadInterval) == 0)
                {
                    raiseEvent_onReadInterval(this, csvRecord);

                    // NOTE: Uncomment profiler lines to do performance testing
                    // readTimer.Print(this.rowsTotal + " records read.");
                }

                // Call onRecordRead event for each record
                raiseEvent_onRecordRead(this, csvRecord, validationResult);
            }

            reader.Close();

            // Call onFileComplete event
            this.completed = true;
            raiseEvent_onFileComplete(this);
        }


        /// <summary>
        /// Resets the data stream and reader, and clears the datatable
        /// </summary>
        public void Reset()
        {
            // Reset data stream and reader
            this.dataStream.Position = 0;
            this.reader.DiscardBufferedData();

            // Reset completed flag
            this.completed = false;

            // Clear hashes, errors, and dupes
            this.recordHashes = new HashSet<string>();
            this.duplicateRecords = new Dictionary<string, List<string>>();
            this.errorRecords = new List<List<string>>();

            // Reset counters
            this.BadRowCount = 0;
            this.GoodRowCount = 0;
            this.TotalRowCount = 0;
            this.DuplicateRowCount = 0;

            // Call onReset event
            raiseEvent_onReset(this);
        }

        /// <summary>
        /// writes data to the specified stream as a CSV
        /// </summary>
        /// <param name="dataStream">the stream to write the data to</param>
        /// <param name="csvData">the data to convert to CSV</param>
        public void Write(Stream dataStream, bool withHeaders = true)
        {
            // Don't write if we haven't read anything
            if (csvData == null)
            {
                throw new Exception("No CSV data has been read!");
            }

            // Write data
            StreamWriter writer = new StreamWriter(dataStream);

            // Write header
            string headerLine = "";
            foreach (DataColumn dc in csvData.Columns)
            {
                headerLine += charDelimiter + "" + charQuote + dc.ColumnName + charQuote;
            }
            headerLine = headerLine.TrimStart(charDelimiter);
            writer.WriteLine(headerLine);

            // Write data
            foreach (DataRow dr in csvData.Rows)
            {
                string finalLine = "";
                foreach (string fieldValue in dr.ItemArray)
                {
                    finalLine += this.charDelimiter + "" + this.charQuote + "" + fieldValue.Replace("" + this.charQuote, (this.charEscapeQuote + "" + this.charQuote)) + "" + this.charQuote;
                }
                finalLine = finalLine.TrimStart(this.charDelimiter);
                writer.WriteLine(finalLine);
            }

            writer.Flush();
            writer.Close();
        }


        // ######################################################################
        //  FORMAT - DATATABLE
        // ######################################################################

        #region DataTable Storage Format - ToDataTable()

        // Data storage
        protected DataTable csvData = null;

        /// <summary>
        /// Sets onRecordRead and onReset handlers, then reads all records from
        /// CSV and populates a new DataTable with the records, and returns the
        /// resulting DataTable.
        /// </summary>
        /// <returns>DataTable containing CSV data</returns>
        public DataTable ToDataTable(bool runAsync = false)
        {
            if (csvData == null)
            {
                // Set record handlers
                this.onRecordRead = this.onRecordRead_ToDataTable;
                this.onReset = this.onReset_ToDataTable;
                this.recordValidator = this.defaultRecordValidator;

                // Define DataTable structure
                csvData = new DataTable(dataName);
                for (int i = 0; i < this.firstRecord.Count; i++)
                {
                    DataColumn dc = new DataColumn();
                    dc.ColumnName = (hasHeaders ? this.firstRecord[i] : "" + i);
                    csvData.Columns.Add(dc);
                }

                // Read records if needed (triggers events) and return resulting DataTable
                this.ReadAllRecords(runAsync);
            }

            return this.csvData;
        }

        public static DataTable LoadIntoDataTable(string Filename, bool HasHeaders = true, bool checkForDupes = false, char charDelimiter = ',', char charQuote = '"', char charEscapeQuote = '\\', Encoding fileEncoding = null)
        {
            if (fileEncoding == null) { fileEncoding = Encoding.UTF8; }
            CSV instance = new CSV(Filename, HasHeaders, checkForDupes, charDelimiter, charQuote, charEscapeQuote, fileEncoding);
            return instance.ToDataTable();
        }

        public static DataTable TableSample(DataTable srcTable, int RowsToSample, bool Distributed = true)
        {
            // Get samples from beginning, middle and end
            DataTable dtSamples;
            if (srcTable.Rows.Count > RowsToSample)
            {
                dtSamples = srcTable.Clone();

                if (!Distributed)
                {
                    // Non-distributed sample, read from beginning to limit (or end of table, whichever comes first)
                    int i = 0;
                    foreach (DataRow dr in srcTable.Rows)
                    {
                        if (i >= RowsToSample) { break; }
                        dtSamples.Rows.Add(dr.ItemArray);
                    }
                }
                else if (Distributed)
                {
                    // Distributed sample, read from different sections throughout the table

                    // Example: srcTable = 999 record DataTable
                    //          RowsToSample = 10
                    //
                    // Result: 0, 109, 219, 329, 439, 549, 659, 769, 879, 998 (zero-index)

                    // Calculate indexes to pull
                    List<int> SampleIndexes = new List<int>();
                    int SkipRows = (int)Math.Round((double)srcTable.Rows.Count / (double)RowsToSample);
                    int SampleIndex = 0;
                    for (int CurrentRowIndex = 0; CurrentRowIndex < srcTable.Rows.Count; CurrentRowIndex += SkipRows)
                    {
                        double PercentProgress = (double)CurrentRowIndex / (double)srcTable.Rows.Count;
                        SampleIndex = CurrentRowIndex + (int)Math.Round((double)PercentProgress * (double)SkipRows) - 1;
                        SampleIndex = Math.Min(srcTable.Rows.Count, (Math.Max(0, SampleIndex)));
                        SampleIndexes.Add(SampleIndex);
                    }

                    // Replace last index with the last record
                    SampleIndexes.Remove(SampleIndex);
                    SampleIndexes.Add(srcTable.Rows.Count - 1);

                    // Copy rows
                    foreach (int _SampleIndex in SampleIndexes)
                    {
                        dtSamples.Rows.Add(srcTable.Rows[_SampleIndex].ItemArray);
                    }
                }
            }
            else
            {
                dtSamples = srcTable;
            }

            return dtSamples;
        }

        /// <summary>
        /// Record handler to populate datatable
        /// </summary>
        /// <param name="sender">Event sender</param>
        /// <param name="csv">Instance of the CSV class</param>
        /// <param name="csvRecord">Record that was just read from the CSV file</param>
        public void onRecordRead_ToDataTable(object sender, CSV csv, List<string> csvRecord, int validationResult)
        {
            // Determine how to process record based on validation result
            switch (validationResult)
            {
                // Validation passed
                case CSV.VALIDATION_OK:
                    this.GoodRowCount++;

                    // Create new DataRow and add to DataTable
                    int i = 0;
                    for (int attempts = 0; attempts < 2; attempts++)
                    {
                        DataRow dr = this.csvData.NewRow();
                        for (i = 0; i < csvRecord.Count; i++)
                        {
                            dr[i] = csvRecord[i];
                        }
                        this.csvData.Rows.Add(dr);
                        break;
                    }


                    break;

                // Duplicate detected
                case CSV.VALIDATION_DUPLICATE:
                    this.DuplicateRowCount++;

                    // Only keep one copy of the dupes by using the hash key
                    string hash = CSV.SHA256(String.Join("", csvRecord));
                    if (!duplicateRecords.ContainsKey(hash))
                    {
                        this.duplicateRecords.Add(hash, csvRecord);
                    }

                    break;

                // Error detected, pass record and result to error handler
                default:
                    this.BadRowCount++;
                    this.errorRecords.Add(csvRecord);
                    raiseEvent_onRecordError(this, csvRecord, validationResult);
                    break;

            }
        }

        /// <summary>
        /// Record handler to reset/clear datatable
        /// </summary>
        /// <param name="sender">Event sender</param>
        /// <param name="csv">Instance of the CSV class</param>
        public void onReset_ToDataTable(object sender, CSV csv)
        {
            // Clear the DataTable
            this.csvData.Clear();
        }

        #endregion

        // ######################################################################
        //  EVENTS
        // ######################################################################

        #region Event Definitions

        // onError Event
        public delegate void onRecordErrorHandler(object sender, CSV csv, List<string> csvRecord, int errCode);
        public event onRecordErrorHandler onRecordError;
        protected virtual void raiseEvent_onRecordError(CSV csv, List<string> csvRecord, int errCode)
        {
            if (onRecordError != null) onRecordError(this, csv, csvRecord, errCode);
        }

        // onRecordRead Event
        public delegate void onRecordReadHandler(object sender, CSV csv, List<string> record, int validationResult);
        public event onRecordReadHandler onRecordRead;
        protected virtual void raiseEvent_onRecordRead(CSV csv, List<string> record, int validationResult)
        {
            if (onRecordRead != null) onRecordRead(this, csv, record, validationResult);
        }

        // onFileComplete Event
        public delegate void onFileCompleteHandler(object sender, CSV csv);
        public event onFileCompleteHandler onFileComplete;
        protected virtual void raiseEvent_onFileComplete(CSV csv)
        {
            if (onFileComplete != null) onFileComplete(this, csv);
        }

        // onReset Event
        public delegate void onResetHandler(object sender, CSV csv);
        public event onResetHandler onReset;
        protected virtual void raiseEvent_onReset(CSV csv)
        {
            if (onReset != null) onReset(this, csv);
        }

        // onReadInterval Event
        public delegate void onReadIntervalHandler(object sender, CSV csv, List<string> lastRecord);
        public event onReadIntervalHandler onReadInterval;
        protected virtual void raiseEvent_onReadInterval(CSV csv, List<string> lastRecord)
        {
            if (onReadInterval != null) onReadInterval(this, csv, lastRecord);
        }

        #endregion

        // ######################################################################
        //  VALIDATION
        // ######################################################################

        #region Record Validator Callback and Default Function

        // Record Validation Handler
        public delegate int recordValidatorHandler(object sender, CSV csv, List<string> record);
        public event recordValidatorHandler recordValidator;
        protected virtual int call_recordValidatorHandler(CSV csv, List<string> record)
        {
            if (recordValidator != null)
                return recordValidator(this, csv, record);
            else
                return CSV.VALIDATION_OK;   // If no record validator is set, then assume every record is okay (probably not a good idea)
        }

        public int defaultRecordValidator(object sender, CSV csv, List<string> record)
        {
            if (record.Count != this.firstRecord.Count)
            {
                // Too many or too few fields
                return CSV.VALIDATION_ERROR_WRONG_NUMBER_OF_FIELDS;
            }
            else
            {
                // If no duplicate-checking is requested, then return okay
                if (!this.checkForDupes)
                {
                    return CSV.VALIDATION_OK;
                }

                // Check for duplicate
                string hash = CSV.SHA256(String.Join("", record));

                if (recordHashes.Add(hash))
                {
                    // recordHashes.Add(hash);
                    return CSV.VALIDATION_OK;
                }
                else
                {
                    // Duplicate hash detected
                    return CSV.VALIDATION_DUPLICATE;
                }
            }
        }

        #endregion

        // ######################################################################
        //  CSV READING
        // ######################################################################

        /// <summary>
        /// Read a single record from the stream using the current encoding and return it as
        /// a List object containing string values.
        /// 
        /// Handles:
        /// - Quoted values (delimiter, quote, and escape characters defined in the CSV class)
        /// - Multiline records
        /// - Multibyte values (e.g. UTF-8)
        /// - Large files (approx. 22 Mb/s)
        /// </summary>
        /// <returns></returns>
        private long ReadRecordCount = 0;

        // Byte values that will be checked
        int chrCurrent = 0;
        int chrLast = 0;
        int chrDelimiter = -1;
        int chrQuote = -1;
        int chrEscapeQuote = -1;
        int chrCarriageReturn = 13;
        int chrNewLine = 10;
        private Decoder decoder;
        bool isEscapedChar = false;
        bool inQuotes = false;
        StringBuilder fieldValue = new StringBuilder();
        List<string> recordFields = new List<string>();

        public int PercentRead()
        {
            return (int)Math.Round(((double)((double)reader.BaseStream.Position / (double)reader.BaseStream.Length)) * 100);
        }

        public List<string> ReadRecord()
        {
            ReadRecordCount++;

            // States of the reader
            isEscapedChar = false;
            inQuotes = false;

            // Record container and the field container
            recordFields = new List<string>();
            fieldValue.Clear();

            // Line number
            int numLines = 1;
            //int last

            // Multibyte character encoding            
            char[] chrCompleteCurrent = new char[4];

            if (reader.EndOfStream) { return null; }
            while (reader.EndOfStream == false)
            {
                // Get next character
                chrCurrent = this.reader.Read();

                // Handle multibyte characters
                int charCount = decoder.GetChars(new[] { (byte)chrCurrent }, 0, 1, chrCompleteCurrent, 0);
                if (charCount == 0)
                {
                    continue;
                }

                // Check character
                if (chrCurrent == chrQuote)
                {
                    // Special exception - when the escape character is also the quote character, like "I like to say ""Hi!"" to everyone!"
                    if (!isEscapedChar && inQuotes && (chrQuote == chrEscapeQuote) && (chrQuote == reader.Peek()))
                    {
                        // It is - we're dealing with a double-quote escape sequence
                        isEscapedChar = true;
                    }
                    else if (isEscapedChar)
                    {
                        // Append character
                        fieldValue.Append((char)chrCurrent);

                        // Turn off escaping for next chars
                        isEscapedChar = false;
                    }
                    else
                    {
                        // Quoted section beginning or ending - toggle on/off
                        inQuotes = !inQuotes;

                        // If we're ending a quoted value, the next character should be a comma or a line-ending. 
                        // Otherwise, we've just hit the end of a record that was missing an ending quote, so
                        // rewind until we get to the start of the current record.
                        if (!inQuotes)
                        {
                            int nextChar = reader.Peek();
                            if ((nextChar != chrDelimiter) && (nextChar != chrCarriageReturn) && (nextChar != chrNewLine))
                            {
                                // Problem Scenarios
                                // Scenario #1: ABC,"DEF,"GHI"
                                //                     ^^^
                                // Scenario #2: ABC,"DEF","GHI
                                //              JKL,"MNO",PQR
                                //                ^^^

                                // Handle Scenarios by closing quotes
                                if (chrLast == chrDelimiter)
                                {
                                    // Assume the last field didn't close properly. 

                                    // Step 1: Fix last field
                                    string lastFieldValue = fieldValue.ToString();
                                    lastFieldValue = lastFieldValue.TrimEnd((char)chrDelimiter);
                                    recordFields.Add(lastFieldValue);

                                    // Step 2: Start new field (we're resuming quotes)
                                    inQuotes = true;
                                    fieldValue.Clear();
                                }
                            }
                        }
                    }
                }
                else if ((chrCurrent == chrEscapeQuote) && inQuotes)
                {
                    isEscapedChar = true;
                }
                else if (chrCurrent == chrDelimiter)
                {
                    if (inQuotes)
                    {
                        // We're inside quotes, so just append the delimiter
                        fieldValue.Append((char)chrCurrent);
                    }
                    else
                    {
                        // End of field
                        recordFields.Add(fieldValue.ToString());
                        fieldValue.Clear();
                    }
                }
                else if (chrCurrent == chrCarriageReturn)
                {
                    // (DOS-style line endings)

                    // Increment line counter
                    numLines++;

                    // See if the next byte is a newline character, and if so, read it to advance the position
                    bool nextCharIsNewLine = false;
                    if (reader.Peek() == chrNewLine)
                    {
                        nextCharIsNewLine = true;
                        reader.Read();
                    }

                    if (!inQuotes)
                    {
                        // Probable line ending if we aren't in quotes and we've hit a carriage return
                        break;
                    }
                    else
                    {
                        // We're inside quotes, so just append the character
                        fieldValue.Append((char)chrCurrent);
                        if (nextCharIsNewLine)
                        {
                            fieldValue.Append((char)chrNewLine);
                        }
                    }
                }
                else if (chrCurrent == chrNewLine)
                {
                    // (*NIX-style line endings)

                    // Increment line counter
                    numLines++;

                    if (!inQuotes)
                    {
                        // Probable line ending if we aren't in quotes and we've hit a newline
                        break;
                    }
                    else
                    {
                        // We're inside quotes, so just append the character
                        fieldValue.Append((char)chrCurrent);
                    }
                }
                else if (isEscapedChar)
                {
                    // Append character
                    fieldValue.Append((char)chrCurrent);

                    // Turn off escaping for next chars
                    isEscapedChar = false;
                }
                else
                {
                    // Append character
                    fieldValue.Append((char)chrCurrent);
                }

                // Keep track of last character
                chrLast = chrCurrent;
            }

            // Add remaining field
            if ((fieldValue.Length > 0) || (chrLast == chrDelimiter))
            {
                recordFields.Add(fieldValue.ToString());
            }

            // If we find an empty line, skip it and just read the next record
            while ((recordFields.Count == 0) && (reader.EndOfStream != false))
            {
                recordFields = this.ReadRecord();
            }

            return recordFields;
        }



        // ######################################################################
        //  SHA-256 HASHING (FOR DUPE-CHECKING)
        // ######################################################################

        #region SHA-256 Hashing Functions

        /// <summary>
        /// Computes the SHA-256 hash of a string
        /// </summary>
        /// <param name="input">Input string</param>
        /// <returns>SHA-256 hash in string representation</returns>
        protected static string SHA256(string input)
        {
            // Convert byte array version into a string
            string strHash = BitConverter.ToString(SHA256_Raw(input));

            // Return formatted version
            return strHash.Replace("-", "").ToLower();
        }

        /// <summary>
        /// Computes the SHA-256 hash of a string
        /// </summary>
        /// <param name="input">Input string</param>
        /// <returns>SHA-256 hash in byte representation</returns>
        protected static byte[] SHA256_Raw(string input)
        {
            // Convert the inputs from strings to byte arrays
            byte[] bInput = Encoding.UTF8.GetBytes(input);

            // Calculate the hash
            SHA256Managed hasher = new SHA256Managed();
            MemoryStream stream = new MemoryStream(bInput);
            byte[] bHash = hasher.ComputeHash(stream);

            return bHash;
        }

        #endregion
    }

    // Uncomment the below block to gain access to a simple stopwatch for performance testing

    //public class Profiler : IDisposable
    //{
    //    private System.Diagnostics.Stopwatch _stopWatch;

    //    public Profiler()
    //        : this("Untitled")
    //    { }

    //    public Profiler(string title)
    //    {
    //        Console.WriteLine(title);
    //        _stopWatch = new System.Diagnostics.Stopwatch();
    //        _stopWatch.Start();
    //    }

    //    public void Print(string comment)
    //    {
    //        Console.WriteLine("  " + _stopWatch.ElapsedMilliseconds + " ms - " + comment);
    //    }

    //    public void Dispose()
    //    {
    //        _stopWatch.Stop();
    //        Console.WriteLine("  " + _stopWatch.ElapsedMilliseconds + " ms - Total");
    //        _stopWatch = null;
    //    }
    //}

    public class CSVHelper
    {
        // Characters for processing
        public static char charDelimiter = ',';
        public static char charQuote = '"';
        public static char charEscapeQuote = '\\';
        public static int chrDelimiter = (int)charDelimiter;
        public static int chrQuote = (int)charQuote;
        public static int chrEscapeQuote = (int)charEscapeQuote;
        public static int chrCarriageReturn = 13;
        public static int chrNewLine = 10;

        /// <summary>
        /// Takes a single CSV string and returns a List of parsed values. Handles quoted 
        /// values (delimiter, quote, and escape characters defined in the CSV class).
        /// </summary>
        /// <returns>List of parsed values</returns>
        public static string[] ParseCSVString(string strCSV, char chrDelimiter = ',', char chrQuote = '"', char chrEscapeQuote = '\\')
        {
            // States of the reader
            bool isEscapedChar = false;
            bool inQuotes = false;

            // Byte values that will be checked
            int chrCurrent = 0;
            int chrLast = 0;

            // Record container and the field container
            List<string> recordFields = new List<string>();
            StringBuilder fieldValue = new StringBuilder();

            // Reader
            StringReader reader = new StringReader(strCSV);

            // Read all characters
            while ((chrCurrent = reader.Read()) >= 0)
            {
                // Check character
                if (chrCurrent == chrQuote)
                {
                    // Special exception - when the escape character is also the quote character, like "I like to say ""Hi!"" to everyone!"
                    if (!isEscapedChar && inQuotes && (chrQuote == chrEscapeQuote) && (chrQuote == reader.Peek()))
                    {
                        // It is - we're dealing with a double-quote escape sequence
                        isEscapedChar = true;
                    }
                    else if (isEscapedChar)
                    {
                        // Append character
                        fieldValue.Append((char)chrCurrent);

                        // Turn off escaping for next chars
                        isEscapedChar = false;
                    }
                    else
                    {
                        // Quoted section beginning or ending - toggle on/off
                        inQuotes = !inQuotes;

                        // If we're ending a quoted value, the next character should be a comma or a line-ending. 
                        // Otherwise, we've just hit the end of a record that was missing an ending quote, so
                        // rewind until we get to the start of the current record.
                        if (!inQuotes)
                        {
                            int nextChar = reader.Peek();
                            if ((nextChar != chrDelimiter) && (nextChar != chrCarriageReturn) && (nextChar != chrNewLine))
                            {
                                // Problem Scenarios
                                // Scenario #1: ABC,"DEF,"GHI"
                                //                     ^^^
                                // Scenario #2: ABC,"DEF","GHI
                                //              JKL,"MNO",PQR
                                //                ^^^

                                // Handle Scenarios by closing quotes
                                if (chrLast == chrDelimiter)
                                {
                                    // Assume the last field didn't close properly. 

                                    // Step 1: Fix last field
                                    string lastFieldValue = fieldValue.ToString();
                                    lastFieldValue = lastFieldValue.TrimEnd((char)chrDelimiter);
                                    recordFields.Add(lastFieldValue);

                                    // Step 2: Start new field (we're resuming quotes)
                                    inQuotes = true;
                                    fieldValue.Clear();
                                }
                            }
                        }
                    }
                }
                else if ((chrCurrent == chrEscapeQuote) && inQuotes)
                {
                    isEscapedChar = true;
                }
                else if (chrCurrent == chrDelimiter)
                {
                    if (inQuotes)
                    {
                        // We're inside quotes, so just append the delimiter
                        fieldValue.Append((char)chrCurrent);
                    }
                    else
                    {
                        // End of field
                        recordFields.Add(fieldValue.ToString());
                        fieldValue.Clear();
                    }
                }
                else if (chrCurrent == chrCarriageReturn)
                {
                    // (DOS-style line endings)

                    // See if the next byte is a newline character, and if so, read it to advance the position
                    bool nextCharIsNewLine = false;
                    if (reader.Peek() == chrNewLine)
                    {
                        nextCharIsNewLine = true;
                        reader.Read();
                    }

                    if (!inQuotes)
                    {
                        // Probable line ending if we aren't in quotes and we've hit a carriage return
                        break;
                    }
                    else
                    {
                        // We're inside quotes, so just append the character
                        fieldValue.Append((char)chrCurrent);
                        if (nextCharIsNewLine)
                        {
                            fieldValue.Append((char)chrNewLine);
                        }
                    }
                }
                else if (chrCurrent == chrNewLine)
                {
                    // (*NIX-style line endings)

                    if (!inQuotes)
                    {
                        // Probable line ending if we aren't in quotes and we've hit a newline
                        break;
                    }
                    else
                    {
                        // We're inside quotes, so just append the character
                        fieldValue.Append((char)chrCurrent);
                    }
                }
                else
                {
                    // Append character
                    fieldValue.Append((char)chrCurrent);
                }

                // Keep track of last character
                chrLast = chrCurrent;
            }

            // Add remaining field
            if ((fieldValue.Length > 0) || (chrLast == chrDelimiter))
            {
                recordFields.Add(fieldValue.ToString());
            }

            return recordFields.ToArray();
        }

    }
}
