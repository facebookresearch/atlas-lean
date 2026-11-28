# The isolation problem is undecidable for linearly ambiguous probabilistic automata

No algorithm decides, given a probabilistic automaton whose number of accepting runs grows at most linearly with the word length and a threshold $c$, whether the acceptance probabilities of all words stay a fixed positive distance away from $c$.

**Definitions.** Let $\mathcal{P}$ be a [probabilistic automaton](../probabilistic-automata-and-cut-point-languages.md) with transition probabilities $\Delta(q, a)(q')$. A *run* of $\mathcal{P}$ on $w = a_1 \cdots a_n$ is a sequence of states $q_0, q_1, \dots, q_n$, with probability $\prod_{\ell=1}^n \Delta(q_{\ell-1}, a_\ell)(q_\ell)$; it is *accepting* if its probability is positive, it starts in the initial state and it ends in an accepting state, and $\mathcal{P}(w)$ is the sum of the probabilities of the accepting runs on $w$. Write $\mathrm{Run}_{\mathcal{P}}(w)$ for the set of accepting runs on $w$. Then $\mathcal{P}$ is *linearly ambiguous* if there is a polynomial $p$ of degree at most one with $|\mathrm{Run}_{\mathcal{P}}(w)| \le p(|w|)$ for every word $w$. A threshold $c$ is *isolated* for $\mathcal{P}$ if there is $\varepsilon > 0$ such that $|\mathcal{P}(w) - c| > \varepsilon$ for all words $w$; the *isolation problem* asks, given $\mathcal{P}$ and $c$, whether $c$ is isolated.

**Theorem.** The isolation problem is undecidable for linearly ambiguous probabilistic automata with rational transition probabilities and a rational threshold, already for the threshold $c = \tfrac12$: the proof reduces the infinite Post correspondence problem to whether $\tfrac12$ is not isolated.

Whether an automaton is unambiguous, finitely ambiguous or polynomially ambiguous can be decided in polynomial time (Weber and Seidl), so the restriction is effective. The isolation problem for general probabilistic automata was shown undecidable by Bertoni with automata of exponential ambiguity; the emptiness problem is also undecidable for linearly ambiguous probabilistic automata, by two independent results of 2018 quoted in the source, while for finitely ambiguous automata emptiness is decidable. Isolation matters because an isolated cut-point defines a regular language, by [Rabin's reduction theorem](../rabin-s-reduction-theorem-for-isolated-cut-points.md).

## Depends on

- [Probabilistic automata and cut-point languages](../probabilistic-automata-and-cut-point-languages.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The infinite Post correspondence problem is undecidable for instances of size 9](../../../../undecidable-problems/post-correspondence-problem/the-infinite-post-correspondence-problem-is-unde.md)

## Expansion

The proof reduces the infinite Post correspondence problem, which asks, given morphisms $\varphi_1, \varphi_2 : \Sigma^* \to \{0, 1\}^*$, whether some infinite word $w \in \Sigma^\omega$ has $\varphi_1(w) = \varphi_2(w)$ (Ruohonen). With $\mathrm{bin}(a_1 \cdots a_n) = \sum_{i=1}^n a_i 2^{-i}$, a solution exists if and only if for every $\varepsilon > 0$ some nonempty finite word $w$ has $|\mathrm{bin}(\varphi_1(w)) - \mathrm{bin}(\varphi_2(w))| \le \varepsilon$: one direction takes prefixes of the infinite solution, the other applies König's lemma to words whose images agree on longer and longer prefixes. A linearly ambiguous probabilistic automaton computes $\mathrm{bin}$ (Bertoni's automaton computes the reversed value with exponential ambiguity), and combining two such automata gives a linearly ambiguous $\mathcal{P}$ with

$$
\mathcal{P}(w) = \frac{1}{2} \left( \mathrm{bin}(\varphi_1(w)) + 1 - \mathrm{bin}(\varphi_2(w)) \right)
$$

for every nonempty word $w$. On the empty word this $\mathcal{P}$ gives $\tfrac12$ however the initial state is marked, which would make $\tfrac12$ never isolated; so, as a repair of the source's construction, add a fresh non-accepting initial state that moves on each letter as the old initial state does, giving $\mathcal{P}'(\varepsilon) = 0$ and $\mathcal{P}'(w) = \mathcal{P}(w)$ for $w \neq \varepsilon$, with the same ambiguity. Then, for $\mathcal{P}'$, $|\mathcal{P}(w) - \frac{1}{2}| \le \varepsilon$ if and only if $|\mathrm{bin}(\varphi_1(w)) - \mathrm{bin}(\varphi_2(w))| \le 2\varepsilon$, so the threshold $\frac{1}{2}$ is not isolated exactly when the infinite Post correspondence problem has a solution. The reduction thus shows undecidability already for the fixed threshold $\frac{1}{2}$. The linked undecidability result builds instances whose target alphabet has four letters; recoding each target letter by a binary word of length $2$ (an injective morphism of uniform length) gives morphisms into $\{0, 1\}^*$ with the same infinite solutions, which is the form used here.

## Sources

- N. Fijalkow, C. Riveros and J. Worrell, "Probabilistic automata of bounded ambiguity", *Information and Computation* 282:104648, 2022, doi:[10.1016/j.ic.2020.104648](https://doi.org/10.1016/j.ic.2020.104648); numbering of arXiv:2205.08175v2: the definitions of runs and ambiguity in Section 2, and Theorem 2 (isolation for linearly ambiguous automata) with its proof in Section 3, after Theorem 1 (emptiness, quoted from earlier work).
