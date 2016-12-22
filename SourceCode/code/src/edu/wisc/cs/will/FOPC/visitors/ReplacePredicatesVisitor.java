/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.visitors.DefaultFOPCVisitor;
import java.util.Map;

/**
 *
 * @author twalker
 */
public class ReplacePredicatesVisitor extends DefaultFOPCVisitor<Map<PredicateNameAndArity, PredicateNameAndArity>> {

    public static final ReplacePredicatesVisitor REPLACE_PREDICATES_VISITOR = new ReplacePredicatesVisitor();

    @Override
    public Term visitFunction(Function function, Map<PredicateNameAndArity, PredicateNameAndArity> data) {

        PredicateNameAndArity pnaa = function.getPredicateNameAndArity();
        PredicateNameAndArity newPNAA = data.get(pnaa);

        if ( newPNAA != null ) {
            function = function.getStringHandler().getFunction(newPNAA.getPredicateName().name, function.getArguments(), function.getTypeSpec());
        }

        return super.visitFunction(function, data);
    }

    @Override
    public Sentence visitLiteral(Literal literal, Map<PredicateNameAndArity, PredicateNameAndArity> data) {
        PredicateNameAndArity pnaa = literal.getPredicateNameAndArity();
        PredicateNameAndArity newPNAA = data.get(pnaa);

        if ( newPNAA != null ) {
            literal = literal.getStringHandler().getLiteral(newPNAA.getPredicateName().name, literal.getArguments(), literal.getArgumentNames());
        }

        return super.visitLiteral(literal, data);
    }

}
