# Doron–Pyne–Tell: BPL = L on average from hardness for log-space-advice-uniform TC0 with logspace oracles

A family $\{C_n\}$ is **log-space-advice-uniform $\mathrm{TC}^0$ of size $T$** if some machine, given $1^n$ and $C\log T$ bits of advice, runs in space $C\log T$ and prints $C_n$. Assume that for every constant $c$ there are constants $k,d\in\mathbb{N}$, $\delta>0$ and $f\colon\{0,1\}^n\to\{0,1\}$ such that

1. $f$ is computable by logspace-uniform $\mathrm{TC}^0$ circuits of depth $d$ and size $O(n^{k})$, and
2. every log-space-advice-uniform family of $\mathrm{TC}^0$ circuits with oracle gates to a $\mathrm{DSPACE}[c\log n]$ function, of size $n^{c}$ and depth $c\cdot d\cdot k^{2}$, satisfies $\Pr_{x\sim U_n}[C_n(x)\ne f(x)]\ge\delta$ for all large $n$.

Then $\mathrm{BPL}\subseteq\bigcap_{\varepsilon>0}\mathrm{avg}_{\varepsilon}\mathrm{L}$, where $\mathrm{avg}_{\varepsilon}\mathrm{L}$ is the class of languages decided by a deterministic logspace algorithm that on every input either answers correctly or outputs $\bot$, and outputs $\bot$ on at most an $\varepsilon$ fraction of inputs of each length. Moreover, for every $c,c',d$ some language in $\mathrm{L}$ is unconditionally hard for log-space-advice-uniform $(\mathrm{TC}^0)^{\mathrm{DSPACE}[c'\log n]}$ circuits of size $n^{c}$ and depth $d$ (in the worst case).

## Proof sketch

The proof opens up the distinguisher: a BPL machine reads its random bits once, so a distinguisher for a targeted somewhere-PRG built from $f$ evaluated on the input can be simulated by a $\mathrm{TC}^0$ circuit with a logspace oracle whose description is computed in logspace with few advice bits. A local list decoder for the hard function, implemented in deterministic logspace-uniform $\mathrm{TC}^0$, converts such a distinguisher into a circuit approximating $f$, contradicting the assumed average-case lower bound.

## Depends on

- [Deterministic logarithmic space](../../complexity-classes/time-and-space-complexity-classes/log-space.md)

## Proof depends on

- [Targeted pseudorandom generators and targeted hitting-set generators](targeted-prg-and-targeted-hsg.md)
- [Nisan–Wigderson generator](../derandomization/nisanwigderson-generator.md)

## Sources

- Dean Doron, Edward Pyne and Roei Tell, "Opening Up the Distinguisher: A Hardness to Randomness Approach for BPL = L that Uses Properties of BPL", STOC (2024), ECCC TR23-208.
