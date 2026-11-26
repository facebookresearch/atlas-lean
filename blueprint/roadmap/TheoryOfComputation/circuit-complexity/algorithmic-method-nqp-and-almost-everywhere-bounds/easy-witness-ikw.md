# Impagliazzo–Kabanets–Wigderson easy witness lemma for NEXP

If $\mathrm{NEXP} \subseteq \mathrm{P}/\mathrm{poly}$, then every language $L \in \mathrm{NEXP}$ has **succinct witnesses**: for every exponential-time verifier $V$ for $L$ there is $c$ such that every $x \in L$ has a witness $y$ for $V$ whose truth table is computed by a Boolean circuit of size $|x|^c$. Consequently $\mathrm{NEXP} \subseteq \mathrm{P}/\mathrm{poly}$ implies $\mathrm{NEXP} = \mathrm{MA}$.

## Proof sketch

If some verifier had infinitely many instances without succinct witnesses, then guessing an instance and using its witnesses' hardness as a truth table would give, via the Nisan-Wigderson generator, a nondeterministic subexponential-time derandomization of $\mathrm{MA}$ on infinitely many lengths; together with $\mathrm{NEXP} \subseteq \mathrm{P}/\mathrm{poly}$ and Kannan-type diagonalization in the exponential hierarchy this yields a contradiction. The second statement follows by guessing the succinct witness circuit inside an $\mathrm{MA}$ protocol built from the interactive proof for $\mathrm{EXP}$.

## Depends on

- [Polynomial time with polynomial advice](../../complexity-classes/time-and-space-complexity-classes/ppoly.md)

## Proof depends on

- [Non-trivial satisfiability and derandomization algorithms for a circuit class](nontrivial-circuit-analysis.md)
- [Pseudorandom generators against circuits](../../pseudorandomness-and-one-way-functions/derandomization/pseudorandom-generators-against-circuits.md)

## Sources

- R. Impagliazzo, V. Kabanets, A. Wigderson, "In search of an easy witness: exponential time vs. probabilistic polynomial time", Journal of Computer and System Sciences 65 (2002) 672-694.
