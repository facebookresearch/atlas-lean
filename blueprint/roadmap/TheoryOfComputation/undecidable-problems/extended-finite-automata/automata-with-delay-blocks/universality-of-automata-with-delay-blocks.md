# Universality of automata with delay blocks is undecidable

Finite automata whose output symbols may be deferred by fixed discrete delays generate untimed languages whose universality is undecidable, although their emptiness is decidable in linear time.

**Theorem.** A *finite automaton with delay blocks* (ADB) is a tuple $\mathcal A = (L, D, \Sigma, \delta, l_s, L_f)$ with a finite set $L$ of locations, a starting location $l_s$, accepting locations $L_f \subseteq L$, an output alphabet $\Sigma$, a finite set $D \subseteq \mathbb N$ of delays, and a transition relation $\delta : (L \times \Sigma \times D) \cup (L \times \{\epsilon, \mathit{tick}\}) \to 2^L$. A generating run $l_s = l_0 \xrightarrow{\alpha_0} l_1 \cdots \xrightarrow{\alpha_{n-1}} l_n \in L_f$ with $l_{i+1} \in \delta(l_i, \alpha_i)$ outputs, for every label $\alpha_i = (\sigma, t)$, the symbol $\sigma$ at time $t + (\text{number of } \mathit{tick}\text{s among } \alpha_0, \ldots, \alpha_{i-1})$; the generated timed word lists these symbols sorted by their output times, symbols with equal times in the order of generation. The *untimed language* $U(\mathcal A) \subseteq \Sigma^*$ is the set of words obtained from generated timed words by dropping the times. There is no algorithm that decides, given an ADB $\mathcal A$ over $\Sigma$, whether $U(\mathcal A) = \Sigma^*$.

Consequently it is undecidable whether $U(\mathcal A)$ equals a given regular language and whether $U(\mathcal A) \subseteq U(\mathcal A')$ for ADBs $\mathcal A, \mathcal A'$ (Corollaries 1 and 2 of the source). Emptiness of an ADB is decidable in linear time (Proposition 12), and every regular language is the untimed language of an ADB whose delays are all $0$ (Proposition 2).

## Depends on

None.

## Proof depends on

- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

For a Turing machine $T$, encode a computation as $w_0 \# w_1 \# \cdots \# w_n$ with each $w_i$ a configuration. A word fails to be an accepting computation if it is not of this shape, if $w_0$ is not initial, if $w_n$ is not accepting, or if some $w_{i+1}$ does not follow from $w_i$. The first three conditions are regular. For the last, an ADB outputs an arbitrary prefix at time $0$, then outputs $w_i$ at time $0$ and $w_{i+1}$ at time $1$, choosing a symbol of $w_{i+1}$ inconsistent with the move of $T$ by guessing the symbols of $w_i$ around the head, and then an arbitrary suffix at time $2$; the regular parts run at later fixed times. The union of these ADBs generates exactly the words that are not accepting computations of $T$, so $U(\mathcal A) \neq \Sigma^*$ iff $T$ has an accepting computation.

## Sources

- K. Chatterjee, T. A. Henzinger and V. S. Prabhu, "Finite automata with time-delay blocks", in *Proceedings of the Tenth ACM International Conference on Embedded Software (EMSOFT 2012)*, ACM, 2012, pp. 43–52, doi:[10.1145/2380356.2380370](https://doi.org/10.1145/2380356.2380370); read as the extended version arXiv:1207.7019v4, whose numbering is used here: Section 2 (definition of ADBs, generating runs and output languages), Propositions 2, 5 and 12, Proposition 14 with its proof, Corollaries 1 and 2, and Theorem 3.
