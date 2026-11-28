# Pattern languages with regular constraints

A pattern is a word over letters and variables; its erasing language collects the words obtained by substituting arbitrary words, possibly
empty, for the variables, and with regular constraints each variable may only be replaced by words of a given regular language.

Let $\Sigma$ be a finite alphabet and $X$ a countable set of variables disjoint from $\Sigma$. A *pattern* is a nonempty finite word over $\Sigma \cup X$; $\mathrm{var}(p)$ is
the set of variables occurring in $p$. A *substitution* is a morphism $h : (\Sigma \cup X)^* \to \Sigma^*$ with $h(a) = a$ for every letter $a \in \Sigma$. The *erasing
pattern language* and the *non-erasing pattern language* of $p$ are

$$
L_E(p) = \{ h(p) : h \text{ a substitution} \}, \qquad L_{NE}(p) = \{ h(p) : h \text{ a substitution with } h(x) \ne \varepsilon \text{ for all } x \in \mathrm{var}(p) \}.
$$

A *pattern with regular constraints* is a pair $(p, r_p)$ where $r_p$ assigns to each variable $x \in \mathrm{var}(p)$ a regular language $r_p(x) \subseteq \Sigma^*$. A substitution $h$
is *$r_p$-valid* if $h(x) \in r_p(x)$ for every $x \in \mathrm{var}(p)$, and

$$
L_E(p, r_p) = \{ h(p) : h \text{ an } r_p\text{-valid substitution} \}
$$

is the *erasing pattern language with regular constraints*; the non-erasing version $L_{NE}(p, r_p)$ also requires $h(x) \ne \varepsilon$. As an input, each constraint $r_p(x)$ is given by a finite automaton. A pattern is *terminal-free* if it
contains no letters. Without constraints, take $r_p(x) = \Sigma^*$ for every variable.

Inclusion of pattern languages, $L_E(\alpha) \subseteq L_E(\beta)$ or $L_{NE}(\alpha) \subseteq L_{NE}(\beta)$, is undecidable for every alphabet with at least two letters (Jiang
et al. for unbounded alphabets; Freydenberger and Reidenbach, and later work, for fixed alphabets), and so is inclusion with
regular constraints.

## Depends on

None.

## Proof depends on

None.

## Sources

- D. Nowotka and M. Wiedenhöft, "The equivalence problem of E-pattern languages with regular constraints is undecidable", *Theoretical Computer Science* 1083, article 116126, 2026, doi:10.1016/j.tcs.2026.116126; conference version in *Implementation and Application of Automata (CIAA 2024)*, Lecture Notes in Computer Science, pp. 276–288, Springer, 2024, doi:10.1007/978-3-031-71112-1_20. Read in arXiv:2411.07275v1: Section 2 (patterns, substitutions, erasing and non-erasing pattern languages, regular constraints) and the known results of Section 2.2 (Theorem 2 on inclusion and Corollary 3 for regular constraints), with the numbering of that version.
