# Codes from small-bias lists have short correlation lists

Let $(r_z)_{z \in Z}$ be a $\delta$-biased list of vectors in $\{0,1\}^n$, and encode $x \in \{0,1\}^n$ as the word $z \mapsto \langle r_z, x\rangle$. Then the $\pm1$ word of every nonzero message has $\bigl|\sum_z (-1)^{\langle r_z, x\rangle}\bigr| \le \delta |Z|$, so codewords of distinct messages agree on a $\tfrac12 \pm \tfrac{\delta}{2}$ fraction of positions. Moreover there is an absolute constant $C$ such that for every word $T : Z \to \{0,1\}$ at most $O(1/\delta)$ messages $x$ satisfy $\bigl|\sum_z (-1)^{T(z) + \langle r_z, x\rangle}\bigr| \ge C\sqrt{\delta}\,|Z|$: no word correlates noticeably with many codewords.

## Proof sketch

The XOR of two codewords is the codeword of the nonzero sum message, which is $\delta$-balanced. For the list bound, the $\pm1$ codewords scaled by $|Z|^{-1/2}$ are unit vectors with pairwise inner products at most $\delta$ in absolute value; if $t = C\delta^{-1}$ of them had inner product at least $C\sqrt{\delta}$ with the scaled word $T$, the Gram matrix of $T$ and these $t$ vectors, tested against $v = (C^2\delta^{-1/2}, -1, \dots, -1)$, would have $vGv^{\mathsf T} < 0$, contradicting positive semidefiniteness.

Derived (an exact form of the same argument, not stated in the cited sources): for all $\gamma, \delta \ge 0$ the number $N$ of messages $x$ with $\bigl|\sum_z (-1)^{T(z) + \langle r_z, x\rangle}\bigr| \ge \gamma|Z|$ satisfies $N(\gamma^2 - \delta) \le 1$, by expanding $\|\sum_x \pm c_x\|^2 \ge (\sum_x |\langle T, c_x\rangle|)^2$ to get $N^2\gamma^2 \le N + N(N-1)\delta$.

## Depends on

- [Small-bias distribution and generator](../space-bounded-and-small-bias-generators/small-bias-distributions.md)

## Sources

- D. M. Kane and R. Williams, "Super-Linear Gate and Super-Quadratic Wire Lower Bounds for Depth-Two and Depth-Three Threshold Circuits", Proceedings of the 48th ACM Symposium on Theory of Computing, 633–643, 2016 (numbering of arXiv:1511.07860), Proposition 2 and its proof (codes from $\varepsilon'$-biased sets: distinct codewords agree on $m(1/2 + O(\varepsilon))$ bits) and Lemma 6.1 with its Gram-matrix proof (at most $O(\varepsilon^{-1})$ codewords with $|rh(T,S) - 1/2| > \Omega(\varepsilon^{1/2})$).
- N. Alon, O. Goldreich, J. Håstad and R. Peralta, "Simple Constructions of Almost k-wise Independent Random Variables", Random Structures & Algorithms 3(3), 289–304, 1992, Section 4.
