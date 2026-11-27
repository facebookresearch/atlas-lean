# Deterministic versus nondeterministic linear bounded automata

Is every language accepted by a nondeterministic [linear bounded automaton](../linear-bounded-automata/linear-bounded-automaton.md) also accepted by a
deterministic one? Since a language of nonempty words is context-sensitive exactly when a nondeterministic linear bounded automaton accepts it, this is Kuroda's first
problem on linear bounded automata, equivalently whether nondeterministic and deterministic linear space coincide.

## Depends on

- [Linear bounded automaton](../linear-bounded-automata/linear-bounded-automaton.md)
- [Language of a linear bounded automaton](../linear-bounded-automata/language.md)

## What would settle it

A simulation of every nondeterministic linear bounded automaton by a deterministic linear bounded automaton accepting the same language, or a
language accepted in nondeterministic linear space but not in deterministic linear space.

## Status

The cited source, which settles Kuroda's question on complementation, states that whether nondeterministic space equals deterministic space is still
unknown; this page does not certify its present status.

## Sources

- N. Immerman, "Nondeterministic space is closed under complementation", *SIAM Journal on Computing* 17(5):935–938, 1988 (author's version): the introduction (Kuroda's question) and the section on conclusions and directions for future work.
