# Ren–Santhanam: KT is hard on average iff one-way functions exist in NC0

Bounded-error average-case hardness of KT over uniformly random strings is equivalent to the existence of one-way functions computable in DLOGTIME, a uniform version of $\mathsf{NC}^0$, and to average-case hardness of the $\mathsf{NC}^1$ and logspace variants of $\mathrm{K}^t$.

Here "hard on average" is bounded-error hardness over the uniform distribution against probabilistic polynomial-time algorithms, and a function family is in DLOGTIME if each output bit is computed by a Turing machine in time $O(\log n)$ with random access to the input. The following are equivalent:

1. There is a one-way function computable in $\oplus\mathsf{L}$.
2. There is a one-way function computable in DLOGTIME.
3. The search version of $\mathrm{KT}$ is hard on average.
4. For every constant $\lambda>0$, $\mathrm{KT}$ is hard on average to approximate within an additive error of $\lambda\log n$.
5. There is a polynomial $t$ such that the search version of $\mathsf{NC}^1\text{-}\mathrm{K}^t$ is hard on average.
6. For every constant $\lambda>0$ and every polynomial $t$ with $t(n)>2n$, $\mathsf{NC}^1\text{-}\mathrm{K}^t$ is hard on average to approximate within an additive error of $\lambda\log n$.
7. There is a polynomial $t$ such that the search version of $\mathsf{L}\text{-}\mathrm{K}^t$ is hard on average.
8. For every constant $\lambda>0$ and every polynomial $t$ with $t(n)>2n$, $\mathsf{L}\text{-}\mathrm{K}^t$ is hard on average to approximate within an additive error of $\lambda\log n$.

Since one-way functions in $\oplus\mathsf{L}$ yield one-way functions in DLOGTIME (Applebaum–Ishai–Kushilevitz), a one-way function exists in uniform $\mathsf{NC}^1$ if and only if $\mathrm{KT}$ is bounded-error hard on average. Hence polynomial-time one-way functions imply $\mathsf{NC}^0$ one-way functions if and only if average-case hardness of $\mathrm{K}^t$ implies average-case hardness of $\mathrm{KT}$.

## Expansion

(3) implies (2): for most strings $x$ the time component $t(x)$ of an optimal KT description is $O(\log n)$, since $\mathrm{K}(x)\ge n-O(\log n)$ for most $x$ while $\mathrm{KT}(x)\le n+O(\log n)$. The function that takes a length, a time bound and a description and outputs the implicitly described string is computable in logarithmic space and its output distribution almost dominates the uniform distribution, so an inverter would solve search-KT on most inputs; it is therefore a weak one-way function, Yao amplification keeps it in logspace, and the randomized-encoding compiler moves it to DLOGTIME. (1) implies (4): a one-way function in $\oplus\mathsf{L}$ gives a conditionally entropy-preserving PRG with stretch $\gamma\log n$ in $\oplus\mathsf{L}$; its perfect randomized encoding is computable in DLOGTIME and stays pseudorandom and entropy preserving, so its outputs have KT complexity $\Theta(\log n)$ below that of random strings, and a $\lambda\log n$ approximator would distinguish. Items 5 to 8 follow the same pattern with the Liu–Pass construction in ALOGTIME and a padding argument.

## Depends on

- [Ren–Santhanam random-access Kt and K^t, parallel variants NC^1-K^t and L-K^t, and average-case hardness](parallel-kolmogorov-complexity-and-kt-average-case-hardness.md)
- [One-way function families](../../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Conditionally entropy-preserving pseudorandom generators from one-way functions](../../meta-complexity-and-one-way-functions/conditionally-entropy-preserving-prgs.md)
- [Degree-3 decomposable randomized encodings of log-depth computations](../../../../ComputerScience/cryptography/public-key/obfuscation-and-witness-encryption/compact-functional-encryption-to-obfuscation/nc0-randomized-encoding.md)
- [Yao's amplification: weak one-way functions yield strong one-way functions](../../one-way-function-transformations/yao-weak-to-strong-amplification.md)

## Sources

- Hanlin Ren and Rahul Santhanam, "Hardness of KT Characterizes Parallel Cryptography", *36th Computational Complexity Conference (CCC 2021)*, LIPIcs, 2021, https://doi.org/10.4230/LIPIcs.CCC.2021.35 (Theorem 1, Theorem 42; Theorems 32, 33 and 36, Section 4).
