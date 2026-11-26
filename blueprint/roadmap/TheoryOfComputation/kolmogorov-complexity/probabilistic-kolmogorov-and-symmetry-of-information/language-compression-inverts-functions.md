# Average-case language compression inverts every polynomial-time function via the universal sampler

If weak average-case language compression holds (with probability at least $1/n^{c}$ for some constant $c$), then infinitely-often one-way functions do not exist: every polynomial-time computable $f$ can be inverted by a probabilistic polynomial-time algorithm with non-negligible success probability on all large input lengths.

## Proof sketch

Given $f$, take $D_n$ to output $(x,f(x))$ for uniform $x$ and $L=\{(x,y):f(x)=y\}$, so $L_y=f^{-1}(y)$. Compression gives $\mathrm{pK}^{p(n)}(x\mid y)\le\log|f^{-1}(y)|+\log p(n)$ for a non-negligible fraction of samples. By the universal-sampler lemma, $\mathrm{USamp}(1^n,1^{p(n)},y)$ outputs each such $x$ with probability $\Omega\bigl(1/(n\,p(n)\,|f^{-1}(y)|)\bigr)$, and summing over the good preimages of a good $y$ shows it outputs some preimage of $y$ with probability $1/\mathrm{poly}(n)$; repetition gives the inverter.

## Depends on

- [Average-case symmetry of information, conditional coding and language compression over samplable pairs](average-case-kolmogorov-principles-over-samplable-pairs.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [The universal time-bounded sampler hits every x with probability about 2^{−pK^t(x|y)}](universal-time-bounded-sampler-and-pkt.md)

## Sources

- Shuichi Hirahara, Rahul Ilango, Zhenjian Lu, Mikito Nanashima and Igor C. Oliveira, "A Duality Between One-Way Functions and Average-Case Symmetry of Information", STOC (2023), ECCC TR23-035.
