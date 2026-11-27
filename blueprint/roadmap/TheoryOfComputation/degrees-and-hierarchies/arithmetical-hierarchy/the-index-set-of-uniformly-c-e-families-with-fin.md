# The index set of uniformly c.e. families with finite teaching dimension is Σ⁰₅-complete

Deciding, for a uniformly computably enumerable family of sets, whether a bounded number of labeled examples always suffices to single out
each member is $\Sigma^0_5$-complete, and the related teaching notions fill levels from $\Pi^0_2$ to $\Sigma^0_5$ of the arithmetical hierarchy.

Fix an effective enumeration $\mathcal{L}_0, \mathcal{L}_1, \dots$ of all uniformly computably enumerable families $\mathcal{L}_e = \{L^e_0, L^e_1, \dots\}$ of subsets of $\mathbb{N}$. A finite set $T \subseteq \mathbb{N} \times \{+, -\}$ of labeled examples is *consistent* with $L$ if $L$ contains every $n$ with
$(n, +) \in T$ and no $n$ with $(n, -) \in T$; it is a *teaching set* for $L \in \mathcal{L}$ if it is consistent with $L$ and with no other member of $\mathcal{L}$. The *teaching dimension* $\mathrm{TD}(L, \mathcal{L})$ is the least size of a teaching set for $L$ (infinite if there is none), and
$\mathrm{TD}(\mathcal{L}) = \sup_{L \in \mathcal{L}} \mathrm{TD}(L, \mathcal{L})$; the *positive* teaching dimension $\mathrm{TD}^+$ uses only positive examples. The index sets are

$$
I_{TD} = \{ e : \mathrm{TD}(\mathcal{L}_e) < \infty \}, \quad I_{TD}^{\forall} = \{ e : \mathrm{TD}(L, \mathcal{L}_e) < \infty \text{ for all } L \in \mathcal{L}_e \}, \quad I_{TD}^{\forall^\infty} = \{ e : \mathrm{TD}(L, \mathcal{L}_e) < \infty \text{ for almost all } L \in \mathcal{L}_e \},
$$

with positive versions $I_{TD^+}$, $I_{TD^+}^{\forall}$ and $I_{TD^+}^{\forall^\infty}$, in the arithmetical hierarchy of classes $\Sigma^0_n$ and $\Pi^0_n$.

**Theorem.**

1. $I_{TD}$, $I_{TD}^{\forall^\infty}$, $I_{TD^+}$ and $I_{TD^+}^{\forall^\infty}$ are $\Sigma^0_5$-complete;
2. $I_{TD}^{\forall}$ and $I_{TD^+}^{\forall}$ are $\Pi^0_4$-complete;
3. the index set of families with finite extended teaching dimension is $\Sigma^0_3$-complete, and with finite positive extended teaching dimension $\Pi^0_2$-complete;
4. the index set of families whose positive recursive teaching dimension is finite, witnessed by a uniformly c.e. teaching sequence, is $\Sigma^0_5$-complete; with teaching sequences of order one it is $\Sigma^0_4$-complete.

The source also shows that the set of triples $(e, x, d)$ with $\mathrm{TD}(L^e_x, \mathcal{L}_e) \le d$ is $\Sigma^0_3$-complete, and the set of triples $(e, x, u)$ such that the $u$-th finite set distinguishes $L^e_x$ from the other members of $\mathcal{L}_e$ is $\Pi^0_2$-complete.

## Depends on

- [The arithmetical class $\Sigma_n$](is-sigma.md)
- [The arithmetical class $\Pi_n$](is-pi.md)

## Proof depends on

None.

## Expansion

The upper bounds come from counting quantifiers in the definitions: for instance $\mathrm{TD}(\mathcal{L}_e) < \infty$ holds iff some bound $a$ works for every member $b$, where "a teaching set of size at most $a$ exists for $L^e_b$" is a $\Sigma^0_3$ condition built from the $\Pi^0_2$-complete property that a finite set
distinguishes a member. Hardness is shown by reducing an arbitrary $\Sigma^0_5$ (respectively $\Pi^0_4$, $\Sigma^0_3$, $\Pi^0_2$) predicate: from an instance one computes a uniformly c.e. family whose teaching dimension is finite exactly when the predicate holds. A complete expansion links the completeness results for the classical index sets of the arithmetical hierarchy that these constructions build on.

## Sources

- A. A. Beros, Z. Gao and S. Zilles, "Classifying the arithmetical complexity of teaching models", in *Algorithmic Learning Theory (ALT 2016)*, Lecture Notes in Computer Science 9925, pp. 145–160, Springer, 2016, doi:10.1007/978-3-319-46379-7_10; read in arXiv:1610.08590v1: the theorems of Section 4 (Teaching Dimension) on the index sets of teaching dimension and extended teaching dimension, Section 5 (Positive Teaching Dimension) and Section 6 (Recursive Teaching Dimension), with the definitions of Section 3.
