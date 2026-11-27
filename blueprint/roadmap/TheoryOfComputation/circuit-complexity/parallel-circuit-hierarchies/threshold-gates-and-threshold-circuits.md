# Threshold gates and the basis of threshold circuits

The *threshold gate* $\mathrm{Th}^m_{\ge j}$ of $m$ arguments outputs $1$ iff at least $j$ of its arguments are $1$; *majority* is $\mathrm{MAJ}_m=\mathrm{Th}^m_{\ge\lceil m/2\rceil}$. A *threshold circuit* is a circuit over the basis of all threshold gates (of every arity and cutoff) together with negation. More generally a *weighted* (linear) threshold gate with real weights $a_1,\dots,a_m$ and threshold $\theta$ outputs $[\sum_i a_iz_i\ge\theta]$.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-synthesis-and-lower-bounds/circuit-models-and-classes/circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)
- [Linear threshold function](../../../Combinatorics/boolean-functions/majority-is-least-stable-conjecture/is-linear-threshold-function.md)
- [Majority function](../../../Combinatorics/boolean-functions/majority-is-least-stable-conjecture/majority.md)

## Sources

- András Hajnal, Wolfgang Maass, Pavel Pudlák et al., "Threshold Circuits of Bounded Depth", Journal of Computer and System Sciences, 1993.
- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
