/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ResThmProver;

/**
 *
 * @author twalker
 */
public enum VariantClauseAction {

    SILENTLY_KEEP_VARIANTS("noAction", false, false),
    WARN_AND_KEEP_VARIANTS("warn", true, false),
    SILENTLY_REMOVE_VARIANTS("silentlyRemove", false, true),
    WARN_AND_REMOVE_VARIANTS("remove", true, true);

    private String parameterSetting;
    private boolean warn;
    private boolean remove;

    VariantClauseAction(String parameterSetting, boolean warn, boolean remove) {
        this.parameterSetting = parameterSetting;
        this.warn = warn;
        this.remove = remove;
    }

    @Override
    public String toString() {
        return parameterSetting;
    }



    public boolean isRemoveEnabled() {
        return remove;
    }

    public boolean isWarnEnabled() {
        return warn;
    }

    public boolean isCheckRequired() {
        return warn || remove;
    }

    public static VariantClauseAction fromString(String setting) {
        for (VariantClauseAction action : values()) {
            if ( setting.toLowerCase().equals(action.parameterSetting.toLowerCase()) ) {
                return action;
            }
        }

        return null;
    }


}
