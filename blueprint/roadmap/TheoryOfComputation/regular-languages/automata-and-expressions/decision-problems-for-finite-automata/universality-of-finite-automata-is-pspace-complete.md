# Universality of nondeterministic finite automata is PSPACE-complete

A nondeterministic finite automaton $\mathcal{A}$ over $\Sigma$ (finitely many states, a set of initial and a set of final states, and a
transition relation labelled by letters) is *universal* if it accepts every word of $\Sigma^*$. The alphabet is part of the input. Deciding whether a given
$\mathcal{A}$ is not universal is decidable in exponential time and is [PSPACE](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)-complete (Meyer and Stockmeyer);
hence so is universality. The upper bound tests the complementary automaton, obtained by the subset construction, for nonemptiness
on the fly: a nondeterministic search guesses a word letter by letter while storing only the current set of states, in polynomial
space, and Savitch's theorem removes the nondeterminism. Nonemptiness itself is in nondeterministic logarithmic space.

## Depends on

- [The complexity class PSPACE](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Savitch theorem](../../../complexity-classes/savitch.md)

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, Lecture Notes in Computer Science 1043, Springer, 1996, pp. 238–266; numbering from the author's posted version, <https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf>: Section 2.3, Proposition 12 (crediting A. R. Meyer and L. J. Stockmeyer, SWAT 1972) and its proof, with Proposition 11 (nonemptiness in nondeterministic logarithmic space).
