# Computable reduction of context-free grammars

- [A form yielding the empty word contains no terminal](terminal-not-mem.md)

## Nullable nonterminals

- [Productions without terminals of an encoded grammar](no-terminals.md)
- [Computed nullable nonterminals of an encoded grammar](nullable.md)
- [Yields of the empty word need only terminal-free productions](yields-no-terminals.md)
- [Terminal-free productions yield only the empty word](eq-nil-of-yields-no-terminals.md)
- [Yields in the terminal-free subgrammar are yields of the grammar](yields-of-yields-no-terminals.md)
- [The nullable nonterminals are computed](mem-nullable-iff.md)

## Removing empty productions

- [Deleting nonterminals from an encoded right-hand side](deletions.md)
- [Computed deletions agree with nullable deletions](mem-nullable-deletions-iff.md)
- [Removing empty productions from an encoded grammar](eps-elim.md)
- [Productions of the computable removal of empty productions](mem-eps-elim-rules.md)
- [Computable removal of empty productions agrees with the classical one](eps-elim-to-cfg.md)
- [Removing empty productions drops only the empty word](language-eps-elim.md)

## Removing unit productions

- [Nonterminals of an encoded grammar](nt-list.md)
- [Target of a unit right-hand side](unit-target.md)
- [One round of unit reachability](unit-step.md)
- [Nonterminals reachable by unit productions in an encoded grammar](unit-reach.md)
- [Unit reachability is computed](mem-unit-reach-iff.md)
- [Unit elimination for encoded grammars](unit-elim.md)
- [Productions of the encoded unit elimination](mem-unit-elim-rules.md)
- [The encoded unit elimination denotes the unit-eliminated grammar](unit-elim-to-cfg.md)

## Reduction

- [Reduction of an encoded grammar](reduce.md)
- [The reduced grammar generates the language minus the empty word](language-reduce.md)
- [The reduced grammar has no empty and no unit productions](is-reduced-reduce.md)

## Primitive recursiveness

- [Reduction is primitive recursive](primrec-reduce.md)
