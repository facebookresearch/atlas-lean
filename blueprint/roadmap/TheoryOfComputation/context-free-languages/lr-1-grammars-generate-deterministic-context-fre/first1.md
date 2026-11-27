# One-letter lookahead of a word

For a word $w$ over an alphabet $T$, the one-letter lookahead $\mathrm{first}_1(w)$ is the first letter of $w$ if $w \ne \varepsilon$, and the end-of-input marker if $w = \varepsilon$:

$$\mathrm{first}_1(a w') = a, \qquad \mathrm{first}_1(\varepsilon) = \text{end of input}.$$

## Sources

- A. V. Aho, M. S. Lam, R. Sethi, and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Chapter 4.
- D. E. Knuth, "On the translation of languages from left to right", *Information and Control* 8 (1965), 607-639.
