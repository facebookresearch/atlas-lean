# Relative Hurewicz theorem: if (X, A) is (n−1)-connected with A simply connected and nonempty and n ≥ 2, then H_i(X, A) = 0 for i < n and the Hurewicz map π_n(X, A) → H_n(X, A) is an isomorphism

Let $n \ge 2$ and let $(X, A)$ be a pair of spaces with $A$ nonempty and simply connected. Suppose $(X, A)$ is $(n-1)$-connected: every path component of $X$ meets $A$, and $\pi_i(X, A, x_0) = 0$ for $1 \le i \le n-1$ and all $x_0 \in A$. Then the relative singular homology satisfies $H_i(X, A) = 0$ for all $i < n$. Moreover, for $x_0 \in A$ the relative Hurewicz map $h\colon \pi_n(X, A, x_0) \to H_n(X, A)$ is a group isomorphism. This map sends the class of $f\colon (D^n, S^{n-1}, s_0) \to (X, A, x_0)$ to $f_*(\beta)$, for a fixed generator $\beta$ of $H_n(D^n, S^{n-1})$.

## Proof sketch

Use CW approximation of pairs, the fact that weak homotopy equivalences induce homology isomorphisms, the five lemma on the long exact sequences of homotopy and homology, and naturality of the Hurewicz map. Together they reduce the claim to a CW pair $(X, A)$. Since $(X, A)$ is $(n-1)$-connected and $A$ is $1$-connected, the quotient comparison for CW pairs makes $\pi_i(X, A) \to \pi_i(X/A)$ an isomorphism for $i \le n$, so $X/A$ is $(n-1)$-connected. A CW pair is a good pair, so $H_i(X, A) \cong \tilde H_i(X/A)$. The Hurewicz theorem for $X/A$, with naturality of Hurewicz maps under the quotient map, gives the claim; the Hurewicz maps involved are natural for compatible choices of the generators of $H_n(D^n, S^{n-1})$. In the lowest case $n = 2$, where $\pi_1(A) = \pi_1(X) = 0$, the pointed set $\pi_1(X, A)$ is a single point and $\pi_2(X, A)$ is a quotient of the abelian group $\pi_2(X)$, so the five lemma is applied to abelian groups only.

## Expansion

A good expansion of this node links each prerequisite of its statement and proof: CW approximation of pairs; CW pairs are good pairs; the comparison of the homotopy groups of a connected CW pair with those of its quotient; Five lemma; the homology of a good pair and of its quotient; Long exact sequence of a pair; Long exact sequence of homotopy groups of a pair; Naturality of the Hurewicz map; Hurewicz theorem; weak homotopy equivalences induce isomorphisms in homology; n-connected pair (X, A); Relative homology groups H\_n(X, A) of a pair of spaces; Relative homotopy group π\_n(X, A, x\_0), n ≥ 1; the relative Hurewicz map; simply connected spaces.

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Theorems 4.32 and 4.37.
