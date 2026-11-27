# Parity games are in NP ∩ coNP, via progress-measure certificates

An encoded parity game $G$ on the positions $\{0, \dots, n-1\}$ is given by an owner for each position (even or odd), a Boolean $n \times n$ move matrix and a priority $\mathrm{pr}(v) \in \mathbb{N}$ for each position. Assume every position has a move, so $G$ is a parity game with winning regions $W_{\mathrm{even}}$ and $W_{\mathrm{odd}}$ (positions from which the player has a winning positional strategy), and assume $\mathrm{pr}(v) \le d$ for all $v$.

A candidate measure assigns to each position $u$ either the top element $\top$ or a tuple $\mu(u) \in \mathbb{N}^{d+1}$, indexed by $0, \dots, d$; it is small if every component of every tuple is at most $n$. For $p \le d$, tuples are compared in the truncated lexicographic order at $p$: $a >_p b$ if, scanning the components $d, d-1, \dots, p$, the first component where $a$ and $b$ differ is larger in $a$; and $a \ge_p b$ if $a >_p b$ or $a$ and $b$ agree on all components $\ge p$. An edge $v \to w$ satisfies the progress condition if $\mu(v) = \top$, or both are tuples with $\mu(v) \ge_{\mathrm{pr}(v)} \mu(w)$ when $\mathrm{pr}(v)$ is even and $\mu(v) >_{\mathrm{pr}(v)} \mu(w)$ when it is odd (a tuple at $v$ never satisfies it against $\top$ at $w$). The verifier accepts $\mu$ when every even position has some move satisfying the progress condition and every move from an odd position satisfies it. Its counted version also returns the number of atomic comparisons and move tests it evaluates. Let $B(n, d) = n \bigl( n (1 + c_d) \bigr)$ with $c_d = (d+1)(2 + 2(d+1)) + 2(d+1)$.

The dual game $G^{\ast}$ swaps all owners and adds $1$ to all priorities. The compressed game $G^{c}$ keeps owners and moves and replaces each priority $q$ by $2r + (q \bmod 2)$, where $r$ is the number of distinct priorities occurring in $G$ that are smaller than $q$.

The following holds, for every position $v$.

1. $v \in W_{\mathrm{even}}(G)$ if and only if there is a small candidate measure $\mu$ with entries in $\mathbb{N}^{d+1}$, accepted by the verifier on $G$, with $\mu(v) \ne \top$.
2. $v \in W_{\mathrm{odd}}(G)$ if and only if there is a small candidate measure with entries in $\mathbb{N}^{d+2}$, accepted by the verifier on $G^{\ast}$, with $\mu(v) \ne \top$.
3. For every candidate measure on $G$, the counted verifier returns the verifier's answer at cost at most $B(n, d)$; on $G^{\ast}$, at cost at most $B(n, d+1)$.
4. $v \in W_{\mathrm{even}}(G)$ if and only if $v \in W_{\mathrm{even}}(G^{c})$.
5. For every candidate measure with entries in $\mathbb{N}^{2n+1}$, the counted verifier on $G^{c}$ has cost at most $B(n, 2n)$.

Together these give polynomial-size certificates, checkable in $O(n^4)$ counted steps after compression, for both winning regions, placing parity games in $\mathsf{NP} \cap \mathsf{coNP}$.

## Sources

- E. A. Emerson and C. S. Jutla, "Tree automata, mu-calculus and determinacy", *Proceedings of FOCS 1991*, 368-377.
- M. Jurdziński, "Small progress measures for solving parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301.
- W. Zielonka, "Infinite games on finitely coloured graphs with applications to automata on infinite trees", *Theoretical Computer Science* 200 (1998), 135-183.
