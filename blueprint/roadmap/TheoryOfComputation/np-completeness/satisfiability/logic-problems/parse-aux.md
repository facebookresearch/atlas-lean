# Reading one negation-free formula

Read one formula built from equalities, conjunctions, disjunctions and existential quantifiers, inside $k$ existential quantifiers, from the front of a token list, returning it with the unread tokens. The first argument is recursion fuel: the read fails when the fuel runs out, at the end of the list, at a token whose code is above $3$, or at a term code that gives no term.
