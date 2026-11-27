# Alternating automata are exponentially more succinct than nondeterministic automata

For $n \ge 1$ let $\Delta_n$ be the set of words over $\{a, b\}$ having two different letters at distance $n$ from each other. Then
$\{a, b\}^* \setminus \Delta_n$ is accepted by an [alternating automaton](alternating-automata-on-finite-words.md) with $2n + 3$ states, but every
nondeterministic finite automaton accepting it has at least $2^n$ states. Hence the exponential blow-up in translating alternating automata
into nondeterministic ones cannot be avoided.

## Depends on

- [Alternating automata on finite words](alternating-automata-on-finite-words.md)

## Proof depends on

- [Complementing alternating automata by dualization](complementing-alternating-automata-by-dualization.md)

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, Lecture Notes in Computer Science 1043, Springer, 1996, pp. 238–266; numbering from the author's posted version, <https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf>: Section 2.5, the example of the languages $\Delta_n$ after Proposition 16 and its fooling argument.
