# DNF and CNF size lower bounds from isolated inputs; parity needs $2^{n-1}$ terms

If $g : \{0,1\}^n \to \{0,1\}$ has $t$ isolated true inputs, then every DNF formula computing $g$ has at least $t$ terms, and each term true at an isolated true input mentions all $n$ variables. Dually a CNF formula computing $g$ has at least as many clauses as $g$ has isolated false inputs. In particular every DNF and every CNF formula for the parity of $n$ variables has at least $2^{n-1}$ terms (clauses), each of width $n$.

## Proof sketch

A term true at an isolated true input $x$ cannot omit a variable, since flipping that variable keeps the term true but makes $g$ false; so the term is true only at $x$, and distinct isolated inputs need distinct terms.

## Depends on

- [Isolated true inputs of a Boolean function](isolated-true-inputs.md)
- [Disjunctive normal form](../../../../../Logic/propositional-logic/boolean-clones-and-cnf-encodings/cnf-gadgets-and-encodings/disjunctive-normal-form.md)
- [CNF formula](../../../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- S. Jukna, Boolean Function Complexity: Advances and Frontiers, Springer, 2012.
