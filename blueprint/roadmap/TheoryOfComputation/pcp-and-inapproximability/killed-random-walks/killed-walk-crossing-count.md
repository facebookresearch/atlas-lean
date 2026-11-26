# Crossing counts of killed walks factor across the crossed edge

Let $G$ be a $D$-regular multigraph and consider killed walks with $T$ labels and kill signals in $\{0, \dots, q - 1\}$. Conditioned on kill time $\ell < T$, a uniformly random killed walk is a uniformly random walk of length $\ell$. Moreover, for $i < \ell$ and predicates $P$, $Q$ on (dart, label sequence), the number of killed walks with kill time $\ell$ whose $i$-th step crosses a dart $d$, whose reversed first $i$ steps satisfy $P(d, \cdot)$, and whose steps $i+2, \dots, \ell$ satisfy $Q(d, \cdot)$ equals

$$\Bigl(\sum_{d} |\{r : P(d, r)\}|\cdot|\{s : Q(d, s)\}|\Bigr)\cdot D^{T - \ell}\,(q - 1)^{\ell}\, q^{T - \ell - 1}.$$

So, up to truncation, the lengths of the walk before and after a crossed edge are independent, which is what the first-moment count in gap amplification uses.

## Proof sketch

Fix the kill time $\ell$: the signals are forced to be nonzero for $\ell$ steps and zero at step $\ell + 1$, contributing $(q - 1)^\ell q^{T - \ell - 1}$, and the unused labels contribute $D^{T - \ell}$. A walk of length $\ell$ through dart $d$ at step $i$ is determined by its reversed prefix from $d$ and its suffix after $d$, chosen independently.

## Depends on

- [Killed random walks (lazy random walks of truncated geometric length)](killed-random-walk.md)

## Sources

- J. Radhakrishnan, "Gap Amplification in PCPs Using Lazy Random Walks", Automata, Languages and Programming (ICALP 2006), 2006.
- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM, 2007.
