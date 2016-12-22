/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.Utils.condor;

import edu.wisc.cs.will.Utils.Utils;
import java.io.File;  import edu.wisc.cs.will.Utils.condor.CondorFile;
import java.util.logging.Logger;

/**
 *
 * @author twalker
 */
public final class CondorUtilities {

    private CondorUtilities() {
    }

    private static Boolean condor = null;

    private static Boolean chirp = null;

    public static boolean isCondor() {
        if (condor == null) {

            String condorSlot = System.getenv("_CONDOR_SLOT");
            if (condorSlot != null) {
                condor = true;
            }
            else {
                condor = false;
            }

            if (condor == true) {
                Utils.println("% Executing under condor.");
            }
        }

        return condor;
    }

    public static boolean isChirp() {
        if (chirp == null) {
            chirp = false;
            if (isCondor()) {
                // String filename = System.getProperty("chirp.config");
                // This is really a hack!  The chirp is created in either case.  However
                // if we are in same domain file system, we will be in our run directory
                // while the chirp config will be somewhere else.
                // If this breaks, we could probably check if the user.dir == chirp.config dir
                // as a second attempt.
                String filename = System.getProperty("user.dir");
                if (filename != null) {
                    File f = new CondorFile(filename, "chirp.config");
                    chirp = f.exists();
                }
            }

            if (chirp == true) {
                Utils.println("% Using Chirp for IO.");
            }
        }

        return chirp;
    }

    public static File getScratchDirectory() {
        String scratch = System.getenv("_CONDOR_SCRATCH_DIR");

        if ( scratch != null ) {
            return new File(scratch);
        }
        else {
            return null;
        }
    }

//    public static void setupLibraryPath() {
//        try {
//            // if (isCondor()) {
//            String domain = getDomain();
//            String os = System.getProperty("os.name");
//            int bits = Integer.parseInt(System.getProperty("sun.arch.data.model"));
//
//            String osSpecificPath = null;
//
//            if ("biostat.wisc.edu".equals(domain)) {
//                if (os.equalsIgnoreCase("LINUX")) {
//                    if (bits == 32) {
//                        osSpecificPath = "/u/twalker/linux/lib";
//                    }
//                    else {
//                        osSpecificPath = "/u/twalker/linux/x86_64/lib:/u/twalker/linux/x86_64/lib64";
//                    }
//                }
//            }
//            else if ("cs.wisc.edu".equals(domain)) {
//                if (os.equalsIgnoreCase("LINUX")) {
//                    if (bits == 32) {
//                        osSpecificPath = "/afs/cs.wisc.edu/u/t/w/twalker/linux/lib";
//                    }
//                    else {
//                        osSpecificPath = "/afs/cs.wisc.edu/u/t/w/twalker/linux/x86_64/lib:/afs/cs.wisc.edu/u/t/w/twalker/linux/x86_64/lib64";
//                    }
//                }
//            }
//
//            if (osSpecificPath != null) {
//                Logger.getLogger(CondorUtilities.class.getCanonicalName()).info("Adding " + osSpecificPath + " to library path.");
//
//
//                String oldPath = System.getProperty("java.library.path");
//                String newPath = null;
//                if (oldPath == null) {
//                    newPath = osSpecificPath;
//                }
//                else {
//                    newPath = oldPath + ":" + osSpecificPath;
//                }
//
//                System.setProperty("java.library.path", newPath);
//
//            }
//        //  }
//        } catch (Exception ex) {
//            Logger.getLogger(CondorUtilities.class.getCanonicalName()).log(Level.SEVERE, "Error setting library path", ex);
//        }
//    }
//
//    protected static String[] possibleDomains = {"biostat.wisc.edu", "cs.wisc.edu"};
//
//    protected static String getDomain() {
//
//        List<String> hosts = new ArrayList<String>();
//
//        try {
//            Enumeration<NetworkInterface> nets = NetworkInterface.getNetworkInterfaces();
//            for (NetworkInterface netint : Collections.list(nets)) {
//                if (netint.isLoopback() == false) {
//                    Enumeration<InetAddress> inetAddresses = netint.getInetAddresses();
//                    for (InetAddress inetAddress : Collections.list(inetAddresses)) {
//
//                        String hostname = inetAddress.getCanonicalHostName();
//
//                        if (hostname.contains(":") == false) {
//                            if (hostname.contains(".") == false) {
//                                // This really isn't canonical...try to do a lookup a couple full names
//                                search:
//                                for (int i = 0; i < possibleDomains.length; i++) {
//                                    String fullHostname = hostname + "." + possibleDomains[i];
//                                    try {
//                                        InetAddress[] ips = InetAddress.getAllByName(fullHostname);
//
//                                        for (int j = 0; j < ips.length; j++) {
//                                            InetAddress ip = ips[j];
//
//                                            if (ip.getHostAddress().equals(inetAddress.getHostAddress())) {
//                                                // This is it...
//                                                hostname = fullHostname;
//                                                break search;
//                                            }
//
//                                        }
//                                    } catch (UnknownHostException e) {
//                                    }
//                                }
//
//                            }
//
//                            hosts.add(hostname);
//
//                            for (int i = 0; i < possibleDomains.length; i++) {
//                                if (hostname != null && hostname.toLowerCase().endsWith(possibleDomains[i].toLowerCase())) {
//                                    return possibleDomains[i];
//                                }
//                            }
//                        }
//                    }
//                }
//            }
//        } catch (SocketException ex) {
//            Logger.getLogger(CondorUtilities.class.getName()).log(Level.SEVERE, null, ex);
//        }
//
//        String msg = "No compatible domain found for Condor configuration.  Found hosts:";
//        for (String string : hosts) {
//            msg += "\n  " + string;
//        }
//
//        Logger.getLogger(CondorUtilities.class.getName()).warning(msg);
//
//
//        return null;
//    }
}
