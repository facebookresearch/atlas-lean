# Density is undecidable for deterministic pushdown languages

It is undecidable whether every word over the alphabet is an infix of a word accepted by a given deterministic pushdown automaton.

**Theorem.** It is undecidable, given a [deterministic pushdown automaton](../../../context-free-languages/grammars-and-pushdown-automata/deterministic-context-free-languages/is-deterministic.md) accepting $L \subseteq \Sigma^*$, whether $L$ is [infix-dense](prefix-suffix-and-infix-dense-languages.md).

The deterministic automaton needs an unrestricted pushdown: for reversal-bounded nondeterministic pushdown automata infix-density is decidable.

## Depends on

- [Deterministic pushdown automaton](../../../context-free-languages/grammars-and-pushdown-automata/deterministic-context-free-languages/is-deterministic.md)
- [Prefix-dense, suffix-dense and infix-dense languages](prefix-suffix-and-infix-dense-languages.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

With $T$ and $L_{na}(p)$ as for suffix-density, and $\Sigma_1 = \Sigma \cup \{\%, e, \triangleright\}$, the language $L'$ consists of the words $r_m \cdots r_1 \triangleright u_0 y_1 u_1 \cdots y_m u_m$ with $y_j \in T$, $u_i$ without an infix in $T$, and prefix blocks $r_j = \%^{p_j} e^{q_j}$ with $q_j = |u_{j-1}|$ and $y_j \in L_{na}(p_j)$. A deterministic pushdown automaton pushes the prefix, then pops one $e$ per symbol of $u_{j-1}$ and uses the $\%^{p_j}$ part to locate and verify the error in $y_j$. Every word of $\Sigma_1^*$ is an infix of a word of $L'$ if and only if every word of $T$ lies in $L_{na}$, that is, if and only if the fixed machine does not halt on $a^d$.

## Sources

- J. Eremondi, O. H. Ibarra and I. McQuillan, "On the Density of Context-Free and Counter Languages", *International Journal of Foundations of Computer Science* 29(2):233–250, 2018, doi:[10.1142/S0129054118400051](https://doi.org/10.1142/S0129054118400051); numbering of arXiv:1903.03001v1: the proposition on infix-density of $\mathrm{DPDA}$ languages in Section 3 with its proof.
