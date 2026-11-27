# Almost-everywhere circuit lower bounds for promise PostBPE do not algebrize

Some oracle $A$ and its multilinear extension $\tilde A$ make promise $\mathsf{PostBPE}^{\tilde A}$, and hence promise $\mathsf{MA}_{\mathsf{E}}^{\tilde A}$, computable by linear-size $A$-oracle circuits on infinitely many lengths, so almost-everywhere lower bounds for these classes need non-algebrizing techniques.

$\mathsf{pr}\text{-}\mathsf{PostBPE}$ is the class of promise problems decided by probabilistic exponential-time machines with postselection: conditioned on an event that may have exponentially small probability, the machine answers correctly with high probability. A separation $\mathcal{C}\not\subset\mathcal{D}$ does not algebrize if $\mathcal{C}^{\tilde A}\subseteq\mathcal{D}^A$ for some oracle $A$ and low-degree extension $\tilde A$ of $A$.

1. There exist an oracle $A_1$ and its multilinear extension $\tilde A_1$ with $\mathsf{pr}\text{-}\mathsf{PostBPE}^{\tilde A_1}\subseteq\mathrm{i.o.}\text{-}\mathrm{SIZE}^{A_1}[O(n)]$; in particular $\mathsf{pr}\text{-}\mathsf{MA}_{\mathsf{E}}^{\tilde A_1}\subseteq\mathrm{i.o.}\text{-}\mathrm{SIZE}^{A_1}[O(n)]$.
2. For integers $n\ge 1$ and $20n\le m<2^{n/2}$, every $\mathsf{PostBPP}$ communication protocol that solves XOR-Missing-String$(n,m)$ with error at most $2^{-5n}$ has communication complexity $\Omega(m)$; hence every pseudodeterministic $\mathsf{PostBPP}$ protocol for it with error at most $1/3$ needs $\Omega(m/n)$ communication.
3. There exist an oracle $A_2$ and its multilinear extension $\tilde A_2$ with $\mathsf{BPE}^{\tilde A_2}\subseteq\mathrm{SIZE}^{A_2}[O(n)]$ on all input lengths, so $\mathsf{BPE}\not\subseteq\mathsf{P}/\mathrm{poly}$ is not affinely relativizing.

The infinitely-often lower bound $\mathsf{MA}_{\mathsf{E}}\not\subseteq\mathsf{P}/\mathrm{poly}$ of Buhrman, Fortnow and Thierauf does algebrize, so item 1 marks the gap between infinitely-often and almost-everywhere bounds; item 3 improves an earlier barrier that used only a multiquadratic extension.

## Expansion

By the transfer principle, a $\mathsf{PostBPE}^{\tilde A}$ machine trying to output a hard truth table at a given length becomes a $\mathsf{PostBPP}$ communication protocol for XOR-Missing-String on the oracle's two halves. Item 2 rests on a rectangle lemma: for any rectangle $R=\mathcal{X}\times\mathcal{Y}$ of size at least $2^{2nm-m+2}$ and any candidate answer $s$, some subrectangle of size at least $2^{-2n-2}|R|$ consists of inputs on which $s$ is not a solution, so a large rectangle cannot carry a correct answer. For item 1, enumerate time-$2^n$ machines $M_i$, set $n_i=4n_{i-1}$ and $m_i=n_i^{20}$, and let the truth table of $A_1$ at length $2\log m_i$ encode an instance $(X_i,Y_i)$ of XOR-Missing-String$(n_i,m_i)$, half for each first bit. The instance is chosen so that the truth table of $M_i^{\tilde A_1}$ at length $\log n_i$ agrees, on all inputs where the machine obeys the postselection promise, with a non-solution $(X_i)_a\oplus(Y_i)_b$; hardwiring $a$ and $b$ gives an $A_1$-oracle circuit of size $O(\log n_i)$. The full low-error lower bound, not only the pseudodeterministic one, is needed to handle promise problems. Item 3 uses a lower bound against several pseudodeterministic $\mathsf{BPP}$ protocols that may each read the others' inputs and perform win-win analyses.

## Depends on

- [Aaronson-Wigderson: the algebrization barrier](aaronson-wigderson-algebrization.md)
- [Multilinear extension of a Boolean function](multilinear-ext.md)
- [XOR-Missing-String problem](xor-missing-string-problem.md)

## Proof depends on

None.

## Sources

- Lijie Chen, Yang Hu and Hanlin Ren, "New Algebrization Barriers to Circuit Lower Bounds via Communication Complexity of Missing-String", *Innovations in Theoretical Computer Science (ITCS)*, 2026, arXiv:2511.14038v1 (Theorems 1.3, 1.4 and 1.5, Lemma 3.2, Corollary 3.8, Theorem 4.1, Sections 3 and 4).
