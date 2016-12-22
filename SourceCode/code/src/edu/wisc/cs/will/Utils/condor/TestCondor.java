/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.Utils.condor;

import edu.wisc.cs.will.Utils.condor.chirp.ChirpClient;
import java.io.BufferedReader;
import java.io.File;  import edu.wisc.cs.will.Utils.condor.CondorFile;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Map;
import java.util.Properties;

/**
 *
 * @author twalker
 */
public class TestCondor {

    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) throws IOException {


        CondorFileInputStream is1 = new CondorFileInputStream("/tmp/t");
        BufferedReader r1 = new BufferedReader(new InputStreamReader(is1));
        String line = null;
        System.out.println("-----------------------------");
        System.out.println("File /tmp/t:");
        while ((line = r1.readLine()) != null) {
            System.out.println(line);
        }
        System.out.println("-----------------------------");
        System.out.println("");

        if (CondorUtilities.isChirp()) {
            try {
                ChirpClient cc = new ChirpClient();
                String lookup = cc.lookup("/tmp/t");
                System.out.println("Results of lookup /tmp/t: " + lookup);

                lookup = cc.lookup("/tmp/blah");
                System.out.println("Results of lookup /tmp/blah: " + lookup);
            } catch (IOException iOException) {
                System.out.println("Lookup failed: " + iOException);
            }


            File f = new CondorFile(".").getAbsoluteFile();
            System.out.println("I am chirping! I am in " + f.toString());
            System.out.println("ls " + f.toString() + ":");
            String[] files = f.list();
            for (int i = 0; i < files.length; i++) {
                String string = files[i];
                System.out.println("  " + string);
            }
            System.out.println("");

        }

        System.out.println("env:");
        Map<String, String> env = System.getenv();
        for (Map.Entry<String, String> entry : env.entrySet()) {
            System.out.println(" " + entry.getKey() + " = " + entry.getValue());
        }

        System.out.println("");

        System.out.println("system properties:");
        Properties props = System.getProperties();
        for (String propName : props.stringPropertyNames()) {
            System.out.println(" " + propName + " = " + props.getProperty(propName));
        }

        System.out.println("");


        String filename = System.getProperty("chirp.config");
        System.out.println("Chirp.config:" + filename);
        if (filename != null) {
            BufferedReader r = new BufferedReader(new CondorFileReader(new CondorFile(filename)));
            while (true) {
                line = r.readLine();
                if (line == null) {
                    break;
                }
                System.out.println(line);
            }
        }

        // CondorUtilities.setupLibraryPath();

        System.out.println("");

//        int bits = Integer.parseInt(System.getProperty("sun.arch.data.model"));
//        String libname = null;
//        if ( bits == 32 ) {
//            libname = "jnilapack-linux-x86";
//        }
//        else {
//            libname = "jnilapack-linux-x86_64";
//        }
//
//        try {
//            System.loadLibrary(libname);
//            System.out.println("Successfully loaded " + libname);
//        }
//        catch(Throwable e) {
//            System.out.println("Unable to load library " + libname + ": " + e.toString());
//        }

//        if ( LAPACK.getInstance().getClass().getSimpleName().equals("JLAPACK") ) {
//            Logger.getAnonymousLogger().warning("Native LAPACK library not found.  Using Java version.  Calculations may be slow!");
//        }
    }

    private TestCondor() {
    }
}
