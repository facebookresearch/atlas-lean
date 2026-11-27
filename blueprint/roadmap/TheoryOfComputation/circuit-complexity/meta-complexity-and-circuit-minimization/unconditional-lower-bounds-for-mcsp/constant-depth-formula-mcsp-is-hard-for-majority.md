# Constant-depth formula minimization is hard for majority

For every depth $d\ge2$, majority reduces to minimizing depth-$d$ formula size by non-uniform $\mathrm{AC}^0$ truth-table reductions. Hence $(\mathrm{AC}^0_d)$-MCSP is not in $\mathrm{AC}^0[p]$ for any prime $p$.

For $d\ge2$, $\mathrm{AC}^0_d$ denotes depth-$d$ formulas built from unbounded fan-in AND and OR gates of fan-out $1$, whose input leaves are the bits of the input and their negations. The size $|\varphi|$ of such a formula is its number of input leaves, and $\mathrm{CC}_{\mathrm{AC}^0_d}(f)$ is the least size of an $\mathrm{AC}^0_d$ formula computing $f$. Then

$$(\mathrm{AC}^0_d)\text{-MCSP}=\{(T,s) : T \text{ is a truth table and } \mathrm{CC}_{\mathrm{AC}^0_d}(T)\le s\}.$$

**Theorem (Ilango).** Let $d\ge2$. Then $\mathrm{MAJORITY}\le^{\mathrm{AC}^0}_{tt}(\mathrm{AC}^0_d)\text{-MCSP}$, that is, a non-uniform polynomial-size $\mathrm{AC}^0$ truth-table oracle circuit computes majority with oracle access to $(\mathrm{AC}^0_d)$-MCSP. Consequently, for every prime $p$, $(\mathrm{AC}^0_d)\text{-MCSP}\notin\mathrm{AC}^0[p]$.

## Expansion

Formula size under this measure obeys a direct product rule: for functions $f$ and $g$ that are not identically $0$, $h(x,y)=f(x)\wedge g(y)$ has $\mathrm{CC}_{\mathrm{AND}\circ\mathrm{AC}^0_{d-1}}(h)=\mathrm{CC}_{\mathrm{AND}\circ\mathrm{AC}^0_{d-1}}(f)+\mathrm{CC}_{\mathrm{AND}\circ\mathrm{AC}^0_{d-1}}(g)$. The reduction builds truth tables whose exact minimum size, examined modulo a prime, encodes the input weight, with a win-win argument on whether a Lipschitz-type hypothesis about formula size holds. Unlike earlier MCSP reductions, it needs the exact minimum size, not an approximation. The $\mathrm{AC}^0[p]$ lower bound then follows from Razborov and Smolensky.

## Depends on

- [Circuit complexity of a Boolean function and truth tables](../../minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)
- [Majority](../../../complexity-classes/time-and-space-complexity-classes/majority-dec.md)
- [AC0](../../../complexity-classes/time-and-space-complexity-classes/ac0.md)
- [AC0(m): constant-depth circuits with MOD gates](../../../complexity-classes/time-and-space-complexity-classes/ac0-mod.md)

## Proof depends on

- [Razborov: majority is not in AC0(mod 2)](../../razborov-majority-not-in-ac0-mod-two.md)
- [Smolensky's theorem: MOD_q is not in AC0(p)](../../constant-depth-circuit-lower-bounds/smolensky-s-theorem-mod-q-is-not-in-ac0-p.md)

## Sources

- Rahul Ilango, "Approaching MCSP from Above and Below: Hardness for a Conditional Variant and AC0[p]", *Innovations in Theoretical Computer Science Conference (ITCS)*, 2020, https://doi.org/10.4230/LIPIcs.ITCS.2020.34 (Definition 2.1, Lemma 2.3, Theorems 1.6 and 4.1).
