# Peeling large rectangles from deterministic decomposable DAGs

In a DNNF $C$ on variables $X$, the set of inputs accepted by certificates that contain a given gate $g$ (each such certificate is a tree; at $\vee$-gates it keeps exactly one child) is a rectangle with respect to the partition $(\mathrm{var}(C_g),X\setminus\mathrm{var}(C_g))$, where $C_g$ is the sub-DAG rooted at $g$. Eliminating a gate (relabelling it by $0$ and propagating the constant) removes exactly the certificates through it. If $C$ is moreover deterministic (a d-DNNF), every accepted input has a unique certificate, so eliminating $g$ removes exactly the inputs of the rectangle of $g$; peeling gates of balanced scope one after another therefore partitions $f^{-1}(1)$, for $|X|\ge 2$, into at most $|C|$ pairwise disjoint balanced rectangles. For a smooth d-DNNF the number of accepted inputs is computed by one bottom-up pass over the DAG (products at $\wedge$-gates, sums at $\vee$-gates).

## Proof sketch

If two certificates through $g$ accept $b$ and $b'$, replacing the subtree below $g$ in the certificate of $b'$ by the one of $b$ gives a certificate through $g$ that accepts $b|_{\mathrm{var}(C_g)}\cup b'|_{X\setminus\mathrm{var}(C_g)}$, because by decomposability the rest of a certificate through $g$ mentions no variable of $C_g$. Determinism makes certificates unique, so the peeled rectangles are disjoint.

## Depends on

- [Negation normal form circuits, DNNF and d-DNNF](nnf-dnnf-and-d-dnnf.md)
- [Balanced multi-partition rectangle covers](multi-partition-rectangle-covers.md)

## Proof depends on

- [DNNF size bounds the multi-partition rectangle cover number](dnnf-size-bounds-rectangle-cover-number.md)

## Sources

- Adnan Darwiche, "Decomposable Negation Normal Form", Journal of the ACM 48(4), 608–647, 2001.
- Simone Bova, Florent Capelli, Stefan Mengel, Friedrich Slivovsky, "Knowledge Compilation Meets Communication Complexity", Proceedings of the Twenty-Fifth International Joint Conference on Artificial Intelligence (IJCAI 2016), 2016, Theorem 1, Lemma 5 and Theorem 6.
