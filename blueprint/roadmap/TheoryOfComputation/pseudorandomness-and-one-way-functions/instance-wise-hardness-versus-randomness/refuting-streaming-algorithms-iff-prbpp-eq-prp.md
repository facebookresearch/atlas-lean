# Chen–Tell–Williams: refuting low-space streaming algorithms is equivalent to prBPP = prP

The following are equivalent:

1. For some $\varepsilon>0$ and some $f\colon\{0,1\}^*\to\{0,1\}^*$ computable in polynomial time $T$, there is an FP-refuter for $f$ against $\mathrm{str}\text{-}\mathrm{TISP}[T(n)^{1+\varepsilon},n^{\varepsilon}]$.
2. $\mathrm{prBPP}=\mathrm{prP}$.
3. For every class $\mathcal{C}$ of probabilistic RAMs that supports error reduction (majority votes of constantly many runs stay in $\mathcal{C}$) and every $f\in\mathrm{FP}$, if there is a BPP-refuter for $f$ against $\mathcal{C}$ then there is an FP-refuter for $f$ against $\mathcal{C}$.

Many polynomial-time $f$ unconditionally cannot be computed by streaming algorithms of space $o(n)$; the equivalence says that making such lower bounds constructive is exactly as hard as derandomizing $\mathrm{prBPP}$.

## Proof sketch

(2 to 3) derandomizes the BPP-refuter itself, and statement 3 leads back to statement 1 through classes of streaming algorithms that have probabilistic refuters. (1 to 2) runs the Chen–Tell targeted hitting-set generator with a reconstruction procedure that can be implemented as a low-space streaming algorithm given the input; the refuter, applied to that streaming algorithm, deterministically produces an input $x$ on which reconstruction fails, so the generator built from $x$ is a hitting set, and two-sided error is handled as in Chen–Tell.

## Depends on

- [Refuters for a function against a class of probabilistic algorithms](refuter-for-a-function.md)

## Proof depends on

- [Chen–Tell instance-wise reconstruction: a targeted HSG from a shallow logspace-uniform circuit](instance-wise-reconstruction-targeted-hsg.md)
- [Chen–Tell: prBPP = prP from almost-all-inputs hardness of depth-n² logspace-uniform circuits](prbpp-eq-prp-from-almost-all-inputs-hardness.md)

## Sources

- Lijie Chen, Roei Tell and Ryan Williams, "Derandomization vs Refutation: A Unified Framework for Characterizing Derandomization", FOCS (2023), ECCC TR23-105.
