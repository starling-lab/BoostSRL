package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

public enum RelevanceStrength {
	STRONGLY_IRRELEVANT, // Be sure to change getWeakestRelevanceStrength if this is not first.
	IRRELEVANT,
	WEAKLY_IRRELEVANT,   // Be sure to change getMildestNegativeRelevanceStrength if this is not the item just before NEUTRAL.
	NEUTRAL,             // The borderline between positive and negative relevance.
	ISA_OBSERVED_FEATURE,
	WEAKLY_RELEVANT_NEG, // Be sure to change getMildestPositiveRelevanceStrength if this is not the first item that is 'good.'
	WEAKLY_RELEVANT,     
	IS_MENTIONED_INSIDE_ADVICE,
	RELEVANT_NEG,
	RELEVANT,               // Be sure to change getDefaultRelevanceStrength if this is no longer the default.
	STRONGLY_RELEVANT_NEG,
	STRONGLY_RELEVANT,      // For combining all the relevance statements about one example.
	VERY_STRONGLY_RELEVANT_NEG,
	VERY_STRONGLY_RELEVANT, // For combining all the relevance statements about all the examples of one category.
	POSSIBLE_ANSWER_NEG,    // Negate the final answer for use when pos-neg flip-flopped and (b) since the Teacher might be saying why something why something was a NEGATIVE example as opposed to what needed to hold for it to be a POSITIVE example.
	POSSIBLE_ANSWER;        // *Be sure to change getStrongestRelevanceStrength if this is not last.*  This combines all the relevance, including comments positive and negative examples.
		
	RelevanceStrength() { }
	
	public static RelevanceStrength getWeakestRelevanceStrength()         { return STRONGLY_IRRELEVANT; }
	public static RelevanceStrength getMildestNegativeRelevanceStrength() { return WEAKLY_IRRELEVANT;   }
	public static RelevanceStrength getMildestPositiveRelevanceStrength() { return WEAKLY_RELEVANT_NEG; }
	public static RelevanceStrength getStrongestRelevanceStrength()       { return POSSIBLE_ANSWER;     }
	public static RelevanceStrength getDefaultRelevanceStrength()         { return RELEVANT;            }
	public static RelevanceStrength getNeutralRelevanceStrength()         { return NEUTRAL;             }
	

	public static RelevanceStrength getStrongestRelevanceStrength(boolean returnPossibleAnswer) { 
		return (returnPossibleAnswer ? POSSIBLE_ANSWER : STRONGLY_RELEVANT_NEG);  // Special case for dealing with POSSIBLE ANSWERS.
	}
	
	public static RelevanceStrength getRelevanceStrengthFromString(String str) {
		try {
			return RelevanceStrength.valueOf(str);
		} catch (Exception e) {
			Utils.error("Problem converting '" + str + "' to a RelevanceStrength: " + e);
			return NEUTRAL;
		}
	}
	
	public double defaultCost() {
		switch(this) {
		case STRONGLY_IRRELEVANT:        return 10.0;
		case IRRELEVANT:                 return  2.5;
		case WEAKLY_IRRELEVANT:          return  1.2;
		case NEUTRAL:                    return  1.000;
		case ISA_OBSERVED_FEATURE:       return  0.900;
		case WEAKLY_RELEVANT_NEG:        return  0.800;
		case WEAKLY_RELEVANT:            return  0.750;
		case IS_MENTIONED_INSIDE_ADVICE: return  0.700;  
		case RELEVANT_NEG:               return  0.550; // Individual relevance statements.  Break ties in favor of unnegated versions.
		case RELEVANT:                   return  0.500;
		case STRONGLY_RELEVANT_NEG:      return  0.150; // All relevance about an example.
		case STRONGLY_RELEVANT:          return  0.100;
		case VERY_STRONGLY_RELEVANT_NEG: return  0.015; // All relevance about all examples with the samee category.
		case VERY_STRONGLY_RELEVANT:     return  0.010;
		case POSSIBLE_ANSWER_NEG:        return  0.002; // Relevance from combining relevance about ALL examples (i.e., of any category).
		case POSSIBLE_ANSWER:            return  0.001; // Clause length will likely dominate, but in case there is no penalty on that, do not set this to zero.			
		}
		Utils.error("Unknown RelevanceStrength: " + this);
		return 1.0;

	}

	public RelevanceStrength getWeaker() {
		int me = ordinal();
		for (RelevanceStrength rs : RelevanceStrength.values()) {
			int other = rs.ordinal();
			if (me == other + 1) { return rs; }
		}
		return null;
	}
	public RelevanceStrength getStronger() {
		int me = ordinal();
		for (RelevanceStrength rs : RelevanceStrength.values()) {
			int other = rs.ordinal();
			if (me == other - 1) { return rs; }
		}
		return null;
	}

	public RelevanceStrength getOneLowerStrengthAvoidingNegativeStrengths() { // Avoids NEGATIVE strengths.
		RelevanceStrength result = getWeaker();
		if (result == null || result.compareTo(getNeutralRelevanceStrength()) <= 0) { return getNeutralRelevanceStrength(); }
		return result;
	}

	public boolean isLessThanNeutral() {
		return this.compareTo(NEUTRAL) < 0;
	}

	public boolean isLessThanOrEqualToNeutral() {
		return this.compareTo(NEUTRAL) <= 0;
	}

    /** Returns the less relevant strength of rs1 and rs2.
     *
     * The more relevant strength is the strength with the lower ordinal value.
     *
     * @param rs1
     * @param rs2
     * @return
     */
    public static RelevanceStrength getLessRelevant(RelevanceStrength rs1, RelevanceStrength rs2) {
        return rs1.ordinal() < rs2.ordinal() ? rs1 : rs2;
    }

    /** Returns the more relevant strength of rs1 and rs2.
     *
     * The more relevant strength is the strength with the highest ordinal value.
     *
     * @param rs1
     * @param rs2
     * @return
     */
    public static RelevanceStrength getMoreRelevant(RelevanceStrength rs1, RelevanceStrength rs2) {
        return rs1.ordinal() > rs2.ordinal() ? rs1 : rs2;
    }

    public boolean isWeaker(RelevanceStrength that) {
        return this.ordinal() < that.ordinal();
    }

    public boolean isStronger(RelevanceStrength that) {
        return this.ordinal() > that.ordinal();
    }

    public boolean isEqualOrWeaker(RelevanceStrength that) {
        return this.ordinal() <= that.ordinal();
    }

    public boolean isEqualOrStronger(RelevanceStrength that) {
        return this.ordinal() >= that.ordinal();
    }
	
}
