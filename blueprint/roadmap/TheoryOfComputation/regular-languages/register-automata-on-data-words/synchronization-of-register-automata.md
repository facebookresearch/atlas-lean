# Synchronization of nondeterministic register automata is undecidable

No algorithm decides whether a given complete nondeterministic register automaton has a synchronizing data word, that is, a data word that sends every configuration to one and the same configuration.

**Definitions.** Fix an infinite data domain $D$ and a finite alphabet $\Sigma$; a *data word* is a finite word over $\Sigma \times D$. For a finite set $R$ of registers, *register constraints* are given by $\varphi ::= \mathrm{true} \mid {=}r \mid \varphi \wedge \varphi \mid \neg\varphi$ for $r \in R$, where a valuation $\nu : R \to D$ and an input value $d$ satisfy ${=}r$ if $\nu(r) = d$. A *register automaton* $\mathcal{R} = \langle L, R, \Sigma, T \rangle$ (as on the page on [register automata on data words](register-automata-on-data-words.md), here without initial and final locations) has a finite set $L$ of locations and transitions $(\ell, a, \varphi, \mathrm{up}, \ell') \in L \times \Sigma \times \Phi(R) \times 2^R \times L$. A configuration is a pair $(\ell, \nu) \in L \times D^{|R|}$; on input $(a, d)$ the transition may fire if $(\nu, d)$ satisfies $\varphi$, and leads to $(\ell', \nu[\mathrm{up} := d])$, which stores $d$ in the registers of $\mathrm{up}$. Write $\mathrm{post}(S, w)$ for the set of configurations reached from a set $S$ of configurations by the data word $w$. The automaton is *complete* if every configuration has a successor on every input, and *deterministic* if it has at most one. A data word $w \in (\Sigma \times D)^+$ is *synchronizing* for $\mathcal{R}$ if $\mathrm{post}(L \times D^{|R|}, w)$ is a single configuration. The *synchronization problem* asks, given $\mathcal{R}$, whether some synchronizing data word exists.

**Theorem.** The synchronization problem for complete nondeterministic register automata is undecidable (Theorem 9 of the source).

The number of registers is part of the input. With one register the problem is decidable and Ackermann-complete, and for deterministic register automata it is PSPACE-complete in general and NLOGSPACE-complete with one register.

## Depends on

- [Register automata on data words](register-automata-on-data-words.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces from the non-universality problem for nondeterministic register automata with initial and accepting locations (does some data word lie outside the language?), which is undecidable (Demri and Lazić, as cited by the source). Given such an automaton $\mathcal{R}$ with initial location $\ell_{in}$ (whose outgoing transitions update all registers, and made complete with a non-accepting sink), add two locations $\mathit{reset}$ and $\mathit{synch}$ and two letters $\star$ and $\#$, all new transitions updating every register: $\star$ leads from every location of $\mathcal{R}$, and from $\mathit{reset}$, to $\ell_{in}$; $\#$ leads from non-accepting locations to $\mathit{synch}$ and from accepting locations to $\mathit{reset}$; $\mathit{synch}$ loops on every letter and $\mathit{reset}$ loops on every letter except $\star$. If $w$ is not in $L(\mathcal{R})$, then $(\star, d)\,w\,(\#, d)$ synchronizes the new automaton in $\mathit{synch}$. Conversely, any synchronizing word must end in $\mathit{synch}$, and the factor between its last $\star$ and the following $\#$ is a word rejected by $\mathcal{R}$. For one register the converse reduction from synchronization to non-universality gives the Ackermann upper bound.

## Sources

- K. Quaas and M. Shirmohammadi, "Synchronizing Data Words for Register Automata", *ACM Transactions on Computational Logic* 20(2), 2019, article 11, pp. 1–27, doi:[10.1145/3309760](https://doi.org/10.1145/3309760). Read in arXiv:1710.02329v2 ([arXiv](https://arxiv.org/abs/1710.02329v2)), whose numbering is used here: the definitions of register automata and synchronizing data words in Section 2, Lemma 8 (non-universality reduces to synchronization), Theorem 9 (undecidability), and Theorems 3, 5 and 11 for the decidable cases.
- S. Demri and R. Lazić, "LTL with the freeze quantifier and register automata", *ACM Transactions on Computational Logic* 10(3), 2009, article 16, pp. 1–30, doi:[10.1145/1507244.1507246](https://doi.org/10.1145/1507244.1507246) (Theorems 2.7 and 5.4, cited by the first source for the undecidability of non-universality; not read here, cited beside the copy read above).
