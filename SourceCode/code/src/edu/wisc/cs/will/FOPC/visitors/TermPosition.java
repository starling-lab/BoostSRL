/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC.visitors;

/**
 *
 * @author twalker
 */
public class TermPosition {

        public int literalPosition;

        public int termPosition;

        public TermPosition(int literalPosition, int termPosition) {
            this.literalPosition = literalPosition;
            this.termPosition = termPosition;
        }

        @Override
        public boolean equals(Object obj) {
            if (obj == null) {
                return false;
            }
            if (getClass() != obj.getClass()) {
                return false;
            }
            final TermPosition other = (TermPosition) obj;
            if (this.literalPosition != other.literalPosition) {
                return false;
            }
            if (this.termPosition != other.termPosition) {
                return false;
            }
            return true;
        }

        @Override
        public int hashCode() {
            int hash = 7;
            hash = 61 * hash + this.literalPosition;
            hash = 61 * hash + this.termPosition;
            return hash;
        }

        @Override
        public String toString() {
            return "" + literalPosition + ":" + termPosition;
        }
    }
