# MA with one bit of advice lacks fixed-polynomial-size circuits

For every constant $k$ there is a language decided by a polynomial-time Merlin–Arthur protocol with a single bit of advice that has no Boolean circuits of size $n^k$; the hard language can even be taken in $(\mathsf{MA}\cap\mathsf{coMA})/1$.

A language $L$ is in $\mathsf{MA}/1$ if there are a polynomial-time Merlin–Arthur machine $M$ taking one advice bit and a sequence of bits $b_1,b_2,\dots$ such that, for each length $n$, $M$ with advice $b_n$ satisfies the Merlin–Arthur promise on every input of length $n$ and accepts exactly the inputs in $L$ of that length; with a wrong advice bit nothing is required. $\mathrm{SIZE}(s)$ is the class of languages that have Boolean circuits of size at most $s(n)$ on every input length $n$. Then for every constant $k>0$:

1. $\mathsf{MA}/1\not\subseteq\mathrm{SIZE}(n^k)$;
2. $(\mathsf{MA}\cap\mathsf{coMA})/1\not\subseteq\mathrm{SIZE}(n^k)$, where one machine with one advice sequence certifies both membership and non-membership;
3. $(\mathsf{MA}\cap\mathsf{coMA})/1\not\subseteq\mathrm{heur}_{1/2+1/n^k}\text{-}\mathrm{SIZE}(n^k)$, that is, no family of size-$n^k$ circuits agrees with the hard language on more than a $1/2+1/n^k$ fraction of the inputs of each length.

The proof neither relativizes nor naturalizes.

## Expansion

Fix a $\mathsf{PSPACE}$-complete language $L$ with a same-length function-restricted interactive proof: a probabilistic polynomial-time oracle machine that asks oracle queries only of the input's length, accepts with probability $1$ when the oracle is $L$ and $x\in L$, and rejects with probability at least $1/2$ for every oracle when $x\notin L$. If $L$ has polynomial-size circuits, then $\mathsf{PSPACE}\subseteq\mathsf{P}/\mathrm{poly}$, so $\mathsf{PSPACE}=\mathsf{MA}$, and $\mathsf{PSPACE}\not\subseteq\mathrm{SIZE}(n^k)$ by diagonalization.

Otherwise let $s(n)$ be the minimum circuit size of $L$ at length $n$ and pad: $x1^y\in L'$ when $x\in L$, $y>|x|$ is a power of $2$ and $(y+|x|)^{k+1}\le s(|x|)<(2y+|x|)^{k+1}$. The advice bit of length $m$ says whether $m=y+n$ has this property, which depends on $m$ alone. With advice $1$, Merlin sends a circuit of size between $(n+y)^{k+1}$ and $(n+2y)^{k+1}$ for $L$ at length $n$ and Arthur runs the interactive proof with the circuit as the oracle, so $L'\in\mathsf{MA}/1$. Circuits of size $m^k$ for $L'$ would give, by hardwiring the padding, circuits of size below $s(n)$ for $L$ on the infinitely many lengths where $s(n)>(n+1)^{k+1}$, a contradiction. Using a paddable, random self-reducible $\mathsf{PSPACE}$-complete language whose complement also has same-length interactive proofs gives item 2; a mildly hard version of that argument followed by an XOR lemma, with Merlin guessing the parity split of the $t$ blocks and certifying each block, gives item 3.

## Depends on

- [The class MA (Merlin–Arthur)](../../complexity-classes/time-and-space-complexity-classes/ma.md)
- [Circuit complexity of a Boolean function and truth tables](../minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)

## Proof depends on

- [Same-length interactive proof for a PSPACE-complete language](same-length-interactive-proof-for-a-pspace-complete-language.md)

## Sources

- Rahul Santhanam, "Circuit Lower Bounds for Merlin-Arthur Classes", *SIAM Journal on Computing*, 2009, https://doi.org/10.1137/070702680 (Theorems 1, 3 and 16, Lemmas 12, 15 and 20, Sections 3 and 4; numbering of the ECCC Report TR07-005 edition read).
