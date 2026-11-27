# Fischer–Rabin lower bound for Presburger arithmetic

Let PA be the first-order theory of $(\mathbb N, +)$, the set of sentences in the language with $+$ and $=$ (and optionally the constants $0$ and $1$) that are true in the natural numbers, with sentences written over a fixed finite alphabet. There is a constant $c > 0$ such that for every decision procedure for PA, given as a deterministic or nondeterministic program for a Turing machine on the alphabet $\{0, 1\}$, there is an $n_0$ such that for every $n > n_0$ some sentence of length $n$ requires more than $2^{2^{cn}}$ computation steps of the procedure to decide whether it belongs to PA.

## Sources

- M. J. Fischer and M. O. Rabin, "Super-exponential complexity of Presburger arithmetic", MIT Project MAC Technical Memorandum 43, 1974, also in *Complexity of Computation*, SIAM-AMS Proceedings 7:27–41, 1974, transcription at <https://en.wikisource.org/wiki/Index:Super-exponential_Complexity_of_Presburger_Arithmetic_by_Fischer_and_Rabin_(1974)_-_MIT-LCS-TM-043.pdf>, Section 1, Theorem 1 and the remark after it on nondeterministic algorithms, and Section 2 on the model of algorithms.
