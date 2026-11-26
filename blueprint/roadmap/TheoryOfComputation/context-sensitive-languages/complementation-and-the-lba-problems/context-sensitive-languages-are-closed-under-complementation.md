# Context-sensitive languages are closed under complementation

If $L \subseteq T^*$ is the language of a [context-sensitive grammar](../context-sensitive-grammars/is-context-sensitive.md) over a finite
terminal alphabet $T$, then so is $T^+ \setminus L$, the set of nonempty words over $T$ not in $L$; context-sensitive grammars in this sense never
generate the empty word. This settles
the second of Kuroda's problems on linear bounded automata. A language of nonempty words is context-sensitive exactly when it is accepted by a nondeterministic linear
bounded automaton, that is, nondeterministic Turing machines in linear space (Kuroda), and nondeterministic space $s(n) \ge \log n$ is closed under
complementation (Immerman; Szelepcsényi).

## Depends on

- [Context-sensitive grammar](../context-sensitive-grammars/is-context-sensitive.md)
- [Language of an unrestricted grammar](../context-sensitive-grammars/language.md)

## Proof depends on

- [Immerman-Szelepcsenyi theorem: NL = coNL](../../complexity-classes/immerman-szelepcsenyi.md)

## Expansion

This page becomes ready once:

- Kuroda's theorem that the languages of context-sensitive grammars are exactly the languages of nondeterministic linear bounded automata, up to the empty word (proof prerequisite; not yet on the graph)
- Closure of nondeterministic space $s(n) \ge \log n$ under complementation, of which the linked page states the case $s(n) = \log n$ (proof prerequisite; not yet stated)

## Sources

- N. Immerman, "Nondeterministic space is closed under complementation", *SIAM Journal on Computing* 17(5):935–938, 1988 (author's version): the introduction (the consequence for context-sensitive languages and Kuroda's question), the main theorem $\mathrm{NSPACE}[s(n)] = \mathrm{co\text{-}NSPACE}[s(n)]$ for $s(n) \ge \log n$, and the corollary on context-sensitive languages with its proof from Kuroda's theorem.
