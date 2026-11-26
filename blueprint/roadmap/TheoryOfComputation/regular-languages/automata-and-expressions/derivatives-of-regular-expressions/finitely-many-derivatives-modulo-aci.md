# A regular expression has finitely many derivatives modulo ACI

Let $\sim$ be the least congruence on regular expressions that makes $+$ associative, commutative and idempotent:
$r + (s + t) \sim (r + s) + t$, $r + s \sim s + r$ and $r + r \sim r$, closed under reflexivity, symmetry, transitivity, $+$, $\cdot$ and $^*$. Extend the [derivative](brzozowski-derivatives.md) by a letter to words by $\partial_\varepsilon r = r$ and $\partial_{wa} r = \partial_a(\partial_w r)$. For every regular expression $r$
over $\Sigma$, the set $\{[\partial_w r]_\sim : w \in \Sigma^*\}$ of derivatives of $r$ up to $\sim$ is finite (Brzozowski). Since $\sim$-equivalent
expressions have the same language and $\sim$ is preserved by derivatives, these classes are the states of a deterministic finite automaton
with initial state $[r]_\sim$, transitions $[s]_\sim \xrightarrow{a} [\partial_a s]_\sim$ and accepting states the classes of the expressions $s$ with $\mathrm{matchEpsilon}(s)$, that is, whose language contains the empty word, which recognizes $L(r)$; without the
quotient the derivatives of $a^*$ are already pairwise distinct. Comparing the derivative automata of two expressions decides their
equivalence.

## Depends on

- [Brzozowski derivatives of regular expressions](brzozowski-derivatives.md)

## Sources

- T. Nipkow and D. Traytel, "Unified decision procedures for regular expression equivalence", *Interactive Theorem Proving (ITP 2014)*, Lecture Notes in Computer Science 8558, Springer, 2014, author copy <https://www21.in.tum.de/~nipkow/pubs/regex_equiv.pdf>: Section 4.1, the definition of ACI equivalence, the finiteness theorem $\mathit{finite}\,\{[\mathrm{fold\ der}\ w\ r]_\sim \mid w \in (\Sigma\, r)^*\}$, the preservation properties and the interpretation $D_\sim$, with the example of $a^*$ and Figure 1.
