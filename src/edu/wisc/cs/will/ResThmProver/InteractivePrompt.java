/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ResThmProver;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Variable;

/**
 *
 * @author twalker
 */
public class InteractivePrompt {

    private HornClauseContext context;
    
    private BufferedReader input;
    private PrintStream output;

    public InteractivePrompt(HornClauseContext context, BufferedReader reader, PrintStream output) {
        this.context = context;
        this.input = reader;
        this.output = output;
    }
    
    public InteractivePrompt(HornClauseContext context) {
        this.context = context;
        this.input = new BufferedReader(new InputStreamReader( System.in));
        this.output = System.out;
    }

    public void interactivePrompt() {

        while (true) {
            try {
                String query = readQuery();
                if (query == null || query.equals("halt.")) {
                    break;
                }
                proveQuery(query);
            } catch (Exception exception) {
                output.println(exception);
            }
        }
    }

    private  String readQuery() throws IOException {

        String query = null;

        boolean done = false;

            while (!done) {

                if (query == null) {
                    output.print(" ?- ");
                }
                else {
                    output.print(" |  ");
                }
                output.flush();
                String line = input.readLine();

                if (line == null) {
                    query = null;
                    done = true;
                }
                else {

                    line = line.trim();

                    if (query == null) {
                        query = line;
                    }
                    else {
                        query += " " + line;
                    }

                    if (query.endsWith(".")) {
                        done = true;
                    }
                }
            }

        return query;
    }

    private void proveQuery(String query) {
        Proof proof = context.getProof(query);

        BindingList bl = proof.getBindings();

        while( true ) {

            if (bl == null) {
                output.println("no");
                break;
            }
            else if (bl.theta.size() == 0) {
                output.println("yes");
                break;
            }
            else {
                boolean first = true;
                for (Variable variable : bl.theta.keySet()) {
                    if (first == false) {
                        output.println(",");
                    }
                    output.print(variable + " = " + bl.lookup(variable));
                    first = false;
                }

                if ( proof.isProofComplete() ) {
                    output.println(".");
                    output.println("yes");
                    break;
                }
                else {
                    output.print(" ? ");
                }

                try {
                    String line = input.readLine();
                    if (line == null || line.equals(";") == false) {
                        output.println("yes");
                        break;
                    }

                    bl = proof.prove();
                } catch (IOException iOException) {
                    break;
                }
            }
        }
    }
}
