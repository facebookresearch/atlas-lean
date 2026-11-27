# Number of elements of a type, with ∞ for infinite types

The order $|G|$ of a group $G$ is the number of its elements if $G$ is finite, and $|G| = \infty$ if $G$ is infinite. Mathlib defines this count for every type, without using the group structure. For a type $\alpha$, Mathlib's $\operatorname{ENat.card}(\alpha)$ is an element of $\mathbb{N} \cup \{\infty\}$, the natural numbers with a largest element $\infty$ added. If $\alpha$ is finite, it is the number of elements of $\alpha$; if $\alpha$ is infinite, it is $\infty$, whatever the infinite cardinality of $\alpha$, so unlike a cardinal number it does not distinguish countable from uncountable sets. Applied to the type of elements of a group $G$, it gives the familiar order of $G$. This is the order of the group, not the order of an element of the group. It also differs from Mathlib's $\operatorname{Nat.card}$, which counts the elements of a finite type in the same way but assigns $0$ to every infinite type.

## Sources

- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the number of elements of a finite type: `ENat.card_eq_coe_fintype_card`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/SetTheory/Cardinal/Finite.lean#L293-L295.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the value $\infty$ exactly for infinite types: `ENat.card_eq_top`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/SetTheory/Cardinal/Finite.lean#L301.
