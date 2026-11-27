# Promise-MA lacks fixed-polynomial-size circuits

For every constant $k>0$ there is a promise problem in Promise-MA that no family of circuits of size $n^k$ decides on the promise, which strengthens Kannan's lower bound for $\Sigma_2$ and Vinodchandran's for $\mathsf{PP}$.

A promise problem $(Y,N)$, with $Y\cap N=\varnothing$, is in Promise-MA if a polynomial-time Merlin–Arthur machine accepts every input in $Y$ and rejects every input in $N$, with arbitrary behavior elsewhere; a circuit family decides it if it is correct on $Y\cup N$. For an advice length $a(n)$, $\mathsf{MA}/a$ is the class of languages $L$ for which a polynomial-time Merlin–Arthur machine taking $a(n)$ advice bits and a sequence of advice strings $b_n$ satisfy: with advice $b_n$ the machine meets the Merlin–Arthur promise on every input of length $n$ and accepts exactly the inputs in $L$ of that length. Then:

1. If $\mathsf{MA}/O(n)\not\subseteq\mathrm{SIZE}(n^k)$, then Promise-MA $\not\subseteq\mathrm{SIZE}(O(n^k))$.
2. For every constant $k>0$, Promise-MA $\not\subseteq\mathrm{SIZE}(n^k)$.

Because Promise-MA is contained in Promise-AM, Promise-$\mathsf{ZPP}^{\mathsf{NP}}_{\|}$, Promise-$\mathsf{S}_2\mathsf{P}$ and $\mathsf{BPP}_{\mathrm{path}}$, each of these promise classes also lacks circuits of size $n^k$ for every $k$; for each of them the hard problem is decidable with one advice bit.

## Expansion

Item 1 turns advice into input. Let $M$ take $cn$ advice bits and let $b_n$ be the correct advice. An input of length $(c+1)n$, read as $xb$ with $|x|=n$ and $|b|=cn$, is a yes-instance if $M$ with advice $b$ satisfies the promise and accepts $x$, a no-instance if it satisfies the promise and rejects, and outside the promise otherwise; other lengths are outside the promise. Every string $xb_n$ lies in the promise, so a circuit of size $m^k/2^{(c+1)k}$ for the promise problem at length $m=(c+1)n$, with $b_n$ hardwired, decides $L$ at length $n$ with size at most $n^k/2$. Item 2 follows by applying item 1 to the hard $\mathsf{MA}/1$ language.

## Depends on

- [The class MA (Merlin–Arthur)](../../complexity-classes/time-and-space-complexity-classes/ma.md)

## Proof depends on

- [MA with one bit of advice lacks fixed-polynomial-size circuits](ma-with-one-bit-of-advice-lacks-fixed-polynomial-size-circuits.md)

## Sources

- Rahul Santhanam, "Circuit Lower Bounds for Merlin-Arthur Classes", *SIAM Journal on Computing*, 2009, https://doi.org/10.1137/070702680 (Lemma 13 and Theorem 14, Section 3; numbering of the ECCC Report TR07-005 edition read).
