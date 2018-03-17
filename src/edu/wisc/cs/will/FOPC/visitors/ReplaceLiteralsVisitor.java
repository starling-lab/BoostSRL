/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.visitors.DefaultFOPCVisitor;
import java.util.Map;

/**
 *
 * @author twalker
 */
public class ReplaceLiteralsVisitor extends DefaultFOPCVisitor<Map<Literal, Literal>> {

    public static final ReplaceLiteralsVisitor REPLACE_LITERALS_VISITOR = new ReplaceLiteralsVisitor();

    @Override
    public Term visitFunction(Function function, Map<Literal, Literal> data) {
        Literal replacement = data.get(function.asLiteral());

        if ( replacement != null ) {
            function = replacement.asFunction();
        }

        return super.visitFunction(function, data);
    }

    @Override
    public Sentence visitLiteral(Literal literal, Map<Literal, Literal> data) {
        Literal replacement = data.get(literal);

        if ( replacement != null ) {
            literal = replacement;
        }

        return super.visitLiteral(literal, data);
    }

}
