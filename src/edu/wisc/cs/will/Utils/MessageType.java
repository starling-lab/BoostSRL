/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.Utils;

/**
 *
 * @author twalker
 */
public enum MessageType {
    STRING_HANDLER_CREATION,
    STRING_HANDLER_VARIABLE_INDICATOR,
    STRING_HANDLER_PREDICATE_COSTS,

    ISA_HANDLER_TYPE_INFERENCE,

    PARSER_VERBOSE_FILE_INCLUDES,
    PARSER_VERBOSE_LIBRARY_LOADING,
    PARSER_VERBOSE_MODE_LOADING,

    ONION_VERBOSE_LAYER_CREATION,

    SKIP_CLAUSEBASE_STATS,

    ILP_THESHOLDING_VERBOSE,

    ILP_OUTERLOOP,
    ILP_INNERLOOP
}
