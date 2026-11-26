# A timed halting run gives a canonical one-cell output

Let $\Gamma$ be a finite, nonempty tape alphabet and let $M$ be a single-tape Turing machine over $\Gamma$. If, from its initial configuration on an input word $\ell$, $M$ reaches within $T$ steps a configuration $b$ in the halting state whose head reads the symbol $a$, then the canonical one-cell computer of $M$ outputs the one-cell word consisting of the embedded symbol $a$ on the embedded input $\ell$ within $4T + 2|\ell| + 6$ steps. Nothing is assumed about the rest of the tape of $b$ or about runs on other inputs.
