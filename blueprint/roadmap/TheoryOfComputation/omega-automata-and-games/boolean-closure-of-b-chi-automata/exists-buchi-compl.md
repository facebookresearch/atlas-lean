# Büchi automata are closed under complementation

For every finite-state nondeterministic Büchi automaton $A$ over an alphabet $\Sigma$, some
finite-state nondeterministic Büchi automaton $\bar A$ satisfies $L_\omega(\bar A) =
\Sigma^\omega \setminus L_\omega(A)$. No assumption is made on $\Sigma$, whereas the source works over
a finite nonempty alphabet.

Complementing a Büchi automaton is much harder than complementing an automaton on finite
words, even for deterministic automata: making the non-accepting states accepting does not
work, since a run may visit both sets infinitely often. Büchi's construction is doubly
exponential; Sistla, Vardi and Wolper (1987) gave $c^{n^2}$ states, and $2^{O(n \log n)}$ is
optimal (Michel 1988). Only existence is claimed here, with no bound on the number of states.

## Informally uses

- [Complement of an ω-regular language, over any alphabet](compl-any.md): the same
  statement for ω-regular languages.

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 2.2, Proposition 7 and the discussion following it.
