# Cohomology of profinite groups

This node is still to be broken down. It covers the cohomology of profinite groups that the pages on Galois
cohomology use: cohomology with coefficients in discrete modules and continuous cochain cohomology with
coefficients in topological modules, its functoriality, cup products and spectral sequences, cohomological
dimension, and the abstract duality theorems from which local and global Tate duality are derived. It follows
Neukirch–Schmidt–Wingberg, Chapters I–III and VI, Milne's *Class Field Theory*, Chapter II, §4, and Milne's
*Arithmetic Duality Theorems*, Chapter I, §§0–1.

A good expansion has pages for:

1. discrete $G$-modules, the cohomology $H^n(G, A)$ by continuous (homogeneous or inhomogeneous) cochains, and
   its description as the direct limit $\varinjlim_U H^n(G/U, A^U)$ over open normal subgroups (NSW I §2, (1.2.5);
   Milne, *Class Field Theory*, Proposition II.4.2), including the commutation with direct limits of modules;
2. the long exact cohomology sequence and $\delta$-functoriality (NSW (1.3.2)), induced modules and Shapiro's
   lemma (NSW (1.3.7), (1.6.4));
3. cup products and their compatibilities (NSW I §4, (1.4.1)–(1.4.6)), and inflation, restriction and corestriction
   (NSW I §5), with the inflation–restriction (five-term) sequence (NSW (1.6.7)) and the Hochschild–Serre spectral
   sequence (NSW (2.4.1));
4. the cohomology of $\hat{\mathbb{Z}}$: $H^1(\hat{\mathbb{Z}}, A) = A/(\sigma - 1)A$ for a topological generator
   $\sigma$, cohomological dimension $1$ and $\# H^0 = \# H^1$ on finite modules;
5. continuous cochain cohomology of topological $G$-modules, its long exact sequences (NSW II §7, (2.7.1),
   (2.7.2)), its computation as an inverse limit for profinite modules (NSW (2.7.5), (2.7.6)), and Tate's results for
   finitely generated $\mathbb{Z}_\ell$-modules and $\mathbb{Q}_\ell$-vector spaces (NSW (2.7.8)–(2.7.12); Bellaïche,
   Proposition 2.1);
6. cohomological and strict cohomological $p$-dimension and their behaviour under closed and open subgroups (NSW
   III §3, (3.3.1)–(3.3.8)), Serre's criterion (NSW (3.4.5)) and, for Galois groups of fields of characteristic
   different from $p$, the criterion for $\operatorname{cd}_p \le n$ in terms of $H^{n+1}$ and $H^n$ of the
   multiplicative group of the algebraic extensions (NSW (6.5.11)), with Hilbert's Theorem 90 for absolute
   Galois groups;
7. dualizing modules and the abstract duality theorem for profinite groups of finite cohomological dimension
   (NSW III §4, (3.4.6)), and duality relative to a class formation, through the Tate–Nakayama theorem (Milne,
   *Arithmetic Duality Theorems*, Theorem I.0.2, Theorem I.1.3, Theorem I.1.8).

## Proof depends on

- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](restriction-corestriction-inflation-and-tate-s-theorem.md), for the finite-group results from which items 3 and 7 pass to the limit
- [Periodicity of Tate cohomology for finite cyclic groups](tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md), for item 4 at finite levels

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §§2–6; Chapter II,
  §§4 and 7; Chapter III, §§3–4; Chapter VI, §5, at the locators above.
- J. S. Milne, *Class Field Theory*, version 4.03 (2020), <https://www.jmilne.org/math/CourseNotes/CFT.pdf>:
  Chapter II, §4, Proposition 4.2.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, §0 (Theorem 0.2, Theorem 0.3) and §1 (Theorems 1.3 and 1.8).
- J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, Clay Mathematics Institute summer
  school, 2009, <http://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKintro.pdf>: §2.1.1, Proposition 2.1
  and Lemmas 2.1–2.4.
