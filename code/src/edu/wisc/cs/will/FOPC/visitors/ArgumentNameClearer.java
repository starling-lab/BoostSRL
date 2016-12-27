package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.visitors.DefaultFOPCVisitor;

public class ArgumentNameClearer {

    private static final RealClearArgumentNamesVisitor REAL_CLEAR_ARGUMENT_NAMES_VISITOR = new RealClearArgumentNamesVisitor();

    public static <T extends Sentence> T clearArgumentNames(T sentence) {
        return (T) sentence.accept(REAL_CLEAR_ARGUMENT_NAMES_VISITOR, null);
    }

    public static <T extends Term> T clearArgumentNames(T term) {
        return (T) term.accept(REAL_CLEAR_ARGUMENT_NAMES_VISITOR, null);
    }

    private static class RealClearArgumentNamesVisitor extends DefaultFOPCVisitor<Void> {  
 
        @Override
        public Literal visitLiteral(Literal literal, Void data) {
            Literal result = (Literal) super.visitLiteral(literal, data);
            result.setArgumentNames(null);
            return result;
        }

        @Override
        public Term visitFunction(Function function, Void data) {
            Function result = (Function) super.visitFunction(function, data);
            result.setArgumentNames(null);
            return result;
        }
    }

    private ArgumentNameClearer() {
    }
}
