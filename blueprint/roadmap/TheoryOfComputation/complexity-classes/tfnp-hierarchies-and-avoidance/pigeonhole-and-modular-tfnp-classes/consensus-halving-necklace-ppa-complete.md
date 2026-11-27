# Filos-Ratsikas–Goldberg: consensus halving, two-thief necklace splitting and discrete ham sandwich are PPA-complete

(i) $\varepsilon$-CONSENSUS-HALVING is PPA-complete for inverse-exponential $\varepsilon$, the first PPA-completeness result for a problem whose definition involves no explicit circuit. (ii) It remains PPA-complete for some inverse-polynomial $\varepsilon$. (iii) NECKLACE-SPLITTING with $k=2$ thieves is PPA-complete. (iv) DISCRETE HAM SANDWICH is PPA-complete (with coordinates possibly exponentially large). For $k$ thieves, the classes $\mathsf{PPA}_k$ are the main candidates for capturing NECKLACE-SPLITTING, which motivated their structural study.

## Proof sketch

Membership in PPA follows from the Simmons–Su existence proof via Tucker's lemma, since approximate solutions have polynomial bit complexity. Hardness for (i) reduces from 2D-TUCKER (and a variant with monochromatic sides) by encoding the Tucker labelling in the measures of agents so that the cut positions represent a point of a Möbius-strip-like domain; (ii) refines this to a smooth embedding of a high-dimensional Möbius strip that tolerates inverse-polynomial error. Inverse-polynomial consensus halving is polynomial-time equivalent to two-thief necklace splitting, giving (iii), and (iv) follows by a direct embedding of consensus-halving instances into point sets.

## Depends on

- [ε-CONSENSUS-HALVING, NECKLACE-SPLITTING and DISCRETE HAM SANDWICH as explicit total search problems](consensus-halving-necklace-splitting.md)
- [The modular classes PPA_q via BIPARTITE_q and the Buss–Johnson operator & combining two classes](ppa-q-and-the-and-operator.md)

## Proof depends on

- [PPA_q equals the &-combination of PPA_p over the primes p dividing q, and PPA_p is closed under Turing reductions](ppa-q-equals-and-of-ppa-p.md)

## Sources

- Aris Filos-Ratsikas and Paul W. Goldberg, "Consensus Halving is PPA-Complete", STOC (2018), arXiv:1711.04503.
- Aris Filos-Ratsikas and Paul W. Goldberg, "The Complexity of Splitting Necklaces and Bisecting Ham Sandwiches", STOC (2019), arXiv:1805.12559.
- Alexandros Hollender, "The Classes PPA-k: Existence from Arguments Modulo k", WINE (2019), arXiv:1912.03729.
