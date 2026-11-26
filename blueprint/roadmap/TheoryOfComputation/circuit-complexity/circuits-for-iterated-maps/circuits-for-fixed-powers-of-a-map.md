# Circuits for fixed powers of a circuit-computable map

Let $f:\{0,1\}^n\to\{0,1\}^n$ be computed by a Boolean circuit of size $s$, let $T\ge 0$, and let $S\subseteq\{0,1\}^n$ satisfy $f(S)\subseteq S$. For every integer $L$ with $0<L\le |S|$ there is a De Morgan circuit of size at most

$$
40000\Bigl(Ls+(n+1)^3\bigl(L+\tfrac{|S|}{L}+1\bigr)\Bigr)
$$

that agrees with the $T$-fold iterate $f^{T}$ on $S$. Taking $S=\{0,1\}^n$, every fixed power of $f$ has a circuit of size $O\bigl(Ls+(n+1)^3(L+2^n/L)\bigr)$, independently of $T$.

## Proof sketch

Choose at most $|S|/L$ checkpoints such that from every state of $S$ the orbit repeats a state or reaches a checkpoint within $2L$ steps, and hard-wire each checkpoint $h$ together with $f^{T-2L}(h)$. On input $x$, compute the first $2L+1$ states of the orbit with $2L$ copies of the circuit, detect the first checkpoint hit or repetition by sorting records, and reconstruct $f^T(x)$ either from the stored value or from the periodic part of the orbit.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)

## Proof depends on

- [Batcher's odd-even merge sorting network](../../../ComputerScience/sorting-and-searching/sorting-networks/batcher-odd-even-mergesort/odd-even-sorter.md)

## Sources

- Samuel Schlesinger, "Square-root circuit bounds for iterated functions", 2026.
