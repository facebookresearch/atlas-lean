# Universality problem for context-free grammars

## Index codes and list languages

- [Unary code of an index](bit-code.md)
- [Concatenated code of an index sequence](bit-codes.md)
- [List word of an index sequence](list-word.md)
- [List language of a PCP instance](list-lang.md)
- [Concatenated index codes are uniquely decodable](bit-codes-injective.md)
- [A PCP instance is solvable exactly when its top and bottom list languages meet](pcp-iff-exists-mem-list-lang.md)

## The grammar

- [Encoded nonterminal](u-nt.md)
- [Encoded letter terminal](u-letter.md)
- [Encoded bit terminal](u-bit.md)
- [List of all letters](all-letters.md)
- [The letters other than a given letter](others.md)
- [Domino-independent productions of the universality grammar](base-rules.md)
- [The mismatch productions](mismatch-rules.md)
- [The universality grammar](univ-grammar.md)

## The languages of the nonterminals

- [Words of letters](letters-lang.md)
- [Nonempty words of letters](letters1-lang.md)
- [Words of bits](bits-lang.md)
- [Codes of index sequences below $k$](codes-lang.md)
- [The mismatch language](mismatch-lang.md)
- [Malformed words](malformed-lang.md)
- [Intended languages of the nonterminals of the universality grammar](univ-val.md)
- [Evaluating a form with one nonterminal](mem-eval-form-one.md)
- [Evaluating a form with two nonterminals](mem-eval-form-two.md)

## Upper bounds: every production is sound for the intended valuation

- [The intended languages form a valuation of the universality grammar](is-valuation-univ-val.md)

## Lower bounds: the intended words are derivable

- [A word that does not start with $w$ leaves $w$ at some position](exists-mismatch-of-not-prefix.md)
- [Membership in the mismatch productions](mem-mismatch-rules.md)
- [Every mismatched word is derivable from the mismatch nonterminal](mismatch-mem.md)
- [The language of the universality grammar](language-univ-grammar.md)

## The language is the complement of the intersection of the list languages

- [No right symbol directly precedes a left symbol in a left-then-right word](append-inr-inl-ne.md)
- [A bit inside a word of letters followed by bits starts a suffix of the bits](exists-suffix-of-inr.md)
- [Codes of indices below $k$ contain no code of $k$](bit-codes-ne-append-bit-code.md)
- [Malformed words are in no list language](not-mem-list-lang-of-malformed.md)
- [Mismatched words are not in the list language](not-mem-list-lang-of-mismatch.md)
- [Every word is malformed or well formed](malformed-or-well-formed.md)
- [The universality grammar generates every word exactly when PCP has no solution](forall-mem-language-univ-grammar-iff.md)

## The many-one reduction

- [The complement of PCP many-one reduces to universality of context-free grammars](many-one-reducible-not-pcp-univ.md)
