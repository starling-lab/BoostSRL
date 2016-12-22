/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.Utils.condor;

import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.chirp.ChirpClient;
import java.io.File;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.net.URI;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author twalker
 */
public class CondorFile extends File {

    private static ChirpClient chirpClient;

    static {
        setupChirp();
    }

    public CondorFile(URI uri) {
        super(uri);
    }

    public CondorFile(File parent, String child) {
        super(parent, Utils.replaceWildCards(child));
    }

    public CondorFile(String parent, String child) {
        super(Utils.replaceWildCards(parent), Utils.replaceWildCards(child));
    }

    public CondorFile(String pathname) {
        super(Utils.replaceWildCards(pathname));
    }

    private static void setupChirp() {
        if (CondorUtilities.isChirp()) {
            try {
                chirpClient = new ChirpClient();
            } catch (IOException ex) {
                Logger.getLogger(CondorFile.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
    }

    @Override
    public boolean canExecute() {
        if (chirpClient != null) {
            throw new UnsupportedOperationException("Unsupported by Condor/Chirp.");
        }
        return super.canExecute();
    }

    @Override
    public boolean canRead() {
        if (chirpClient != null) {
            throw new UnsupportedOperationException("Unsupported by Condor/Chirp.");
        }
        return super.canRead();
    }

    @Override
    public boolean canWrite() {
        if (chirpClient != null) {
            throw new UnsupportedOperationException("Unsupported by Condor/Chirp.");
        }
        return super.canWrite();
    }

    @Override
    public boolean createNewFile() throws IOException {
        if (chirpClient != null) {
            throw new UnsupportedOperationException("Unsupported by Condor/Chirp.");
        }
        return super.createNewFile();
    }

    @Override
    public boolean delete() {
        if (chirpClient != null) {
            try {
                if ( exists() ) {
                    chirpClient.unlink(getPath());
                    return true;
                }
            } catch (IOException ex) {
                throw new RuntimeException("Condor/Chirp error deleting file " + getPath() + ":" + ex.toString());
            }
            return false;
        }
        else {
            return super.delete();
        }
    }

    @Override
    public boolean exists() {
        if (chirpClient != null) {

            try {
                CondorFileInputStream is = new CondorFileInputStream(this);
                try {
                    is.close();
                } catch (IOException iOException) {
                }
                return true;

            } catch (FileNotFoundException fileNotFoundException) {
                return false;
            }
        }
        else {
            return super.exists();
        }
    }

    @Override
    public long getTotalSpace() {
        if (chirpClient != null) {
            throw new UnsupportedOperationException("Unsupported by Condor/Chirp.");
        }
        return super.getTotalSpace();
    }

    @Override
    public long getUsableSpace() {
        if (chirpClient != null) {
            throw new UnsupportedOperationException("Unsupported by Condor/Chirp.");
        }
        return super.getUsableSpace();
    }

    @Override
    public boolean isDirectory() {
        if (chirpClient != null) {
            throw new UnsupportedOperationException("Unsupported by Condor/Chirp.");
        }
        return super.isDirectory();
    }

    @Override
    public boolean isFile() {
        if (chirpClient != null) {
            throw new UnsupportedOperationException("Unsupported by Condor/Chirp.");
        }
        return super.isFile();
    }

    @Override
    public long lastModified() {
        if (chirpClient != null) {
            throw new UnsupportedOperationException("Unsupported by Condor/Chirp.");
        }
        return super.lastModified();
    }

    @Override
    public long length() {
        if (chirpClient != null) {
            throw new UnsupportedOperationException("Unsupported by Condor/Chirp.");
        }
        return super.length();
    }

    @Override
    public String[] list() {
        if (chirpClient != null) {
            throw new UnsupportedOperationException("Unsupported by Condor/Chirp.");
        }
        return super.list();
    }

    @Override
    public File[] listFiles() {
        if (chirpClient != null) {
            throw new UnsupportedOperationException("Unsupported by Condor/Chirp.");
        }
        return super.listFiles();
    }

    @Override
    public boolean mkdir() {
        if (chirpClient != null) {
            try {
                chirpClient.mkdir(getPath());
                return true;
            } catch (IOException ex) {
                throw new RuntimeException("Condor/Chirp failed to create " + getPath() + ".");
            }
        }
        else {
            return super.mkdir();
        }
    }

    @Override
    public boolean mkdirs() {
        if (chirpClient != null) {
            if (exists() == false) {
                String parentString = getParent();
                if (parentString != null) {
                    File parent = new CondorFile(parentString);
                    parent.mkdirs();
                }

                mkdir();
            }

            return true;
        }
		return super.mkdirs();
    }

    @Override
    public boolean renameTo(File dest) {
        if (chirpClient != null) {
            throw new UnsupportedOperationException("Unsupported by Condor/Chirp.");
        }
        return super.renameTo(dest);
    }

    @Override
    public File getParentFile() {
    	String parent = getParent();
    	if (parent == null) { return null; } // Maybe we should throw an error here?  JWS 10/16/10
        return new CondorFile(parent);
    }


}
