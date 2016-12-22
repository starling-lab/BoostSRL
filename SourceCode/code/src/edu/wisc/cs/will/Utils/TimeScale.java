/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.Utils;

/**
 *
 * @author twalker
 */
public enum TimeScale {

    NaN(Double.NaN, ""),
    YEAR(365 * 24 * 60 * 60, "y"),
    DAY(24* 60 * 60, "d"),
    HOUR(60 * 60, "h"),
    MINUTE(60, "m"),
    SECOND(1,"s"),
    MILLSECOND(1e-3, "ms"),
    MICROSECOND(1e-6, "\u00B5s"),
    NANOSECOND(1e-9, "ns");

    double seconds;
    String unitSymbol;

    private TimeScale(double seconds, String unitSymbol) {
        this.seconds = seconds;
        this.unitSymbol = unitSymbol;
    }

    public double getSeconds() {
        return seconds;
    }

    public String getUnitSymbol() {
        return unitSymbol;
    }

    public double convertTo(double value, TimeScale newScale) {
        return value * ( this.seconds / newScale.seconds );
    }

    public TimeScale getBestTimeScale(double value) {
        return getBestTimeScale(value, NANOSECOND, YEAR);
    }

    public TimeScale getBestTimeScale(double value, TimeScale lowestTimeScale, TimeScale highestTimeScale) {

        if ( Double.isNaN(value) ) {
            return NaN;
        }

        value = Math.abs(value);

        TimeScale aTimeScale = lowestTimeScale;

        for(int i = lowestTimeScale.ordinal(); i >= highestTimeScale.ordinal(); i--) {
            aTimeScale = values()[i];

            double convertedValue = this.convertTo(value, aTimeScale);

            if ( i==0 || (convertedValue > 1 && convertedValue < aTimeScale.nextLongerScale().seconds / aTimeScale.seconds )) {
                break;
            }
        }

        return aTimeScale;
    }

    /** Returns a format string representing the value in the optimal time scale.
     *
     * The format string controls the format of the output.  Three arguments will be passed
     * into the String.format method: the format provided, a double of the converted time
     * value, and a string representing the units.  The units are typically one or two characters
     * long.
     * <p>
     * Some examples of format strings:
     *  "%f%s" - Converted value followed by unit.
     *  "%2$s" - Unit only (the 2$ access the second argument).
     *  "%f"   - Converted value only.
     *
     * @param value
     * @param format
     * @return
     */
    public String getBestFormattedString(double value, String format) {
        return getBestFormattedString(value, format, NANOSECOND, YEAR);
    }

    /** Returns a format string representing the value in the optimal time scale.
     *
     * The format string controls the format of the output.  Three arguments will be passed
     * into the String.format method: the format provided, a double of the converted time
     * value, and a string representing the units.  The units are typically one or two characters
     * long.
     * <p>
     * Some examples of format strings:
     *  "%f%s" - Converted value followed by unit.
     *  "%2$s" - Unit only (the 2$ access the second argument).
     *  "%f"   - Converted value only.
     *
     * @param value
     * @param format
     * @param lowestTimeScale
     * @param highestTimeScale
     * @return
     */
    public String getBestFormattedString(double value, String format, TimeScale lowestTimeScale, TimeScale highestTimeScale) {
        TimeScale bestTimeScale = getBestTimeScale(value, lowestTimeScale, highestTimeScale);

        value = this.convertTo(value, bestTimeScale);

        return String.format(format, value, bestTimeScale.getUnitSymbol());
    }

    public boolean isShorter(TimeScale that) {
        return this.seconds < that.seconds;
    }

    public TimeScale nextShorterScale() {
        return values()[ordinal()+1];
    }

    public TimeScale nextLongerScale() {
        return values()[ordinal()-1];
    }


}
