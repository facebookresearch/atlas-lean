# First-order definable word languages are exactly the star-free languages

Let $\Sigma$ be a finite alphabet and $L \subseteq \Sigma^*$ a language of finite words (the empty word
included). View a word as a finite linear order of positions with a unary predicate for each letter,
and call $L$ first-order definable when it is the set of words satisfying a first-order sentence over
the order and the letter predicates. Call $L$ star-free when it belongs to the smallest family of
languages that contains $\Sigma^*$ and every singleton $\{a\}$ with $a \in \Sigma$ and is closed under
finite union, complement in $\Sigma^*$ and concatenation (no Kleene star). Call $L$ aperiodic when it
is recognized by a morphism to a finite aperiodic monoid, one in which every element $x$ satisfies
$x^{n} = x^{n+1}$ for some $n$. Then the following are equivalent: $L$ is first-order definable; $L$ is star-free; $L$ is
aperiodic. The first equivalence is due to McNaughton and Papert, and the equivalence of star-freeness
and aperiodicity to Schützenberger.

## Depends on

- [Recognition of a language by a monoid morphism](syntactic-monoids/syntactic-monoid/recognizes.md)

## Expansion

A sound expansion builds on the pages for regular languages and syntactic monoids, including the
[syntactic monoid](syntactic-monoids/syntactic-monoid/syntactic-monoid.md), and has separate pages for the
statement prerequisites: first-order logic over finite words, with
the conventions for the empty word; star-free expressions; aperiodic monoids and the characterization
of aperiodicity by the syntactic monoid. It then has pages for Schützenberger's theorem and the
McNaughton–Papert theorem. The extension to infinite words
and the equivalence with linear temporal logic are separate statements.

## Sources

- V. Diekert and P. Gastin, "First-order definable languages", in J. Flum, E. Grädel and T. Wilke
  (eds.), *Logic and Automata: History and Perspectives*, Texts in Logic and Games 2, Amsterdam
  University Press (2007), 261–306, Theorem 1.1 and the discussion after it.
  <http://www.lsv.fr/Publis/PAPERS/PDF/DG-WT08.pdf>
