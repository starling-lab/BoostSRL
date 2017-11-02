/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.Utils.condor;

import java.io.File;

/**
 *
 * @author twalker
 */
public class CompressionUtilities {

    public static File getFile(File originalFile, boolean gzipped) {
        if ( gzipped ) {
            return getGZFile(originalFile);
        }
		return getNonGZFile(originalFile);
    }

    public static File getGZFile(File originalFile) {

        if (originalFile.getName().endsWith(".gz")) {
            return originalFile;
        }
		return new File( originalFile.getParent(), originalFile.getName() + ".gz");
    }
    
    public static File getNonGZFile(File originalFile) {

        if (originalFile.getName().endsWith(".gz")) {
            String gzFileName   = originalFile.getName();
            String noGZFileName = gzFileName.substring(0, gzFileName.length() - 3);

            return new File( originalFile.getParent(), noGZFileName);
        }
		return originalFile;
    }

    private CompressionUtilities() {
    }


}
