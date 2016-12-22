package edu.wisc.cs.will.FOPC;

public class PrettyPrinterOptions {

    /** Enables a new-line after an opening parathesis.
     *
     */
    private int maximumLineWidth = 130;
    
    private int maximumTermsPerLine = -1;

    private int maximumLiteralsPerLine = -1;

    private boolean multilineOutputEnabled = true;

    private boolean renameVariables = true;

    private boolean printClausesAsImplications = false;

    private boolean alignParathesis = true;

    private boolean newLineAfterOpenParathesis = true;

    private int maximumConsCells = -1;

    private String sentenceTerminator = ".";

    private int maximumIndentationAfterImplication = Integer.MAX_VALUE;

    private boolean newLineAfterImplication = false;

    public PrettyPrinterOptions() {
    }

    public PrettyPrinterOptions(boolean renameVariables) {
        this.renameVariables = renameVariables;
    }

    /**
     * @return the maximumLineWidth
     */
    public int getMaximumLineWidth() {
        return maximumLineWidth;
    }

    /**
     * @param maximumLineWidth the maximumLineWidth to set
     */
    public void setMaximumLineWidth(int maximumLineWidth) {
        this.maximumLineWidth = maximumLineWidth;
    }

    /**
     * @return the maximumTermsPerLine
     */
    public int getMaximumTermsPerLine() {
        return maximumTermsPerLine;
    }

    /**
     * @param maximumTermsPerLine the maximumTermsPerLine to set
     */
    public void setMaximumTermsPerLine(int maximumTermsPerLine) {
        this.maximumTermsPerLine = maximumTermsPerLine;
    }

    public int getMaximumLiteralsPerLine() {
        if ( maximumLiteralsPerLine != -1 ) return maximumLiteralsPerLine;
        if ( maximumTermsPerLine != -1 ) return maximumTermsPerLine;
        return -1;
    }

    public void setMaximumLiteralsPerLine(int maximumLiteralsPerLine) {
        this.maximumLiteralsPerLine = maximumLiteralsPerLine;
    }

    /**
     * @return the multilineOutputEnabled
     */
    public boolean isMultilineOutputEnabled() {
        return multilineOutputEnabled;
    }

    /**
     * @param multilineOutputEnabled the multilineOutputEnabled to set
     */
    public void setMultilineOutputEnabled(boolean multilineOutputEnabled) {
        this.multilineOutputEnabled = multilineOutputEnabled;
    }

    /**
     * @return the renameVariables
     */
    public boolean isRenameVariables() {
        return renameVariables;
    }

    /**
     * @param renameVariables the renameVariables to set
     */
    public void setRenameVariables(boolean renameVariables) {
        this.renameVariables = renameVariables;
    }

    /**
     * @return the printClausesAsImplications
     */
    public boolean isPrintClausesAsImplications() {
        return printClausesAsImplications;
    }

    /**
     * @param printClausesAsImplications the printClausesAsImplications to set
     */
    public void setPrintClausesAsImplications(boolean printClausesAsImplications) {
        this.printClausesAsImplications = printClausesAsImplications;
    }

    /**
     * @return the alignParathesis
     */
    public boolean isAlignParathesis() {
        return alignParathesis;
    }

    /**
     * @param alignParathesis the alignParathesis to set
     */
    public void setAlignParathesis(boolean alignParathesis) {
        this.alignParathesis = alignParathesis;
    }

    /**
     * @return the newLineAfterOpenParathesis
     */
    public boolean isNewLineAfterOpenParathesis() {
        return newLineAfterOpenParathesis;
    }

    /**
     * @param newLineAfterOpenParathesis the newLineAfterOpenParathesis to set
     */
    public void setNewLineAfterOpenParathesis(boolean newLineAfterOpenParathesis) {
        this.newLineAfterOpenParathesis = newLineAfterOpenParathesis;
    }

    public int getMaximumConsCells() {
        return maximumConsCells;
    }

    public void setMaximumConsCells(int maximumConsCells) {
        this.maximumConsCells = maximumConsCells;
    }

    public String getSentenceTerminator() {
        return sentenceTerminator;
    }

    public void setSentenceTerminator(String sentenceTerminator) {
        this.sentenceTerminator = sentenceTerminator;
    }

    public int getMaximumIndentationAfterImplication() {
        return maximumIndentationAfterImplication;
    }

    public void setMaximumIndentationAfterImplication(int maximumIndentationAfterImplication) {
        this.maximumIndentationAfterImplication = maximumIndentationAfterImplication;
    }

    public boolean isNewLineAfterImplication() {
        return newLineAfterImplication;
    }

    public void setNewLineAfterImplication(boolean newLineAfterImplication) {
        this.newLineAfterImplication = newLineAfterImplication;
    }

    
}
