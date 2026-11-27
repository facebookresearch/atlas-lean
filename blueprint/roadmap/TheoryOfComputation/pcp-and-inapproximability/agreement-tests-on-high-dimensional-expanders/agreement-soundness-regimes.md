# High-soundness and low-soundness agreement theorems

Fix an agreement test $\mathcal{D}$ on a set family $\mathcal{F}$. It satisfies a **high-acceptance (99%) agreement theorem** with constant $C$ if every ensemble with $\operatorname{Agr}_{\mathcal{D}}(\{f_s\}) \ge 1 - \varepsilon$ is $C\varepsilon$-close to global. It satisfies a **low-acceptance (1%) agreement theorem** with soundness $\delta$ if for every ensemble with $\operatorname{Agr}_{\mathcal{D}}(\{f_s\}) \ge \delta$ there is $G : [n] \to \Sigma$ with

$$
\Pr_{s}\Bigl[\Pr_{i \in s}\bigl[f_s(i) \ne G(i)\bigr] \le \eta\Bigr] \ge \operatorname{poly}(\delta),
$$

that is, for a $\operatorname{poly}(\delta)$-fraction of $s \in \mathcal{F}$, $f_s$ agrees with $G$ on all but an $\eta$-fraction of the coordinates of $s$ (the cited theorems take $\eta = 0.01$). The **list-decoding** variant asks for a short list $G^1, \dots, G^\ell$ covering all heavy agreement.

## Depends on

- [Agreement tests for ensembles of local functions](agreement-test.md)

## Sources

- I. Dinur, D. Steurer, "Direct product testing", CCC (2014), ECCC TR13-179.
- Y. Dikstein, I. Dinur, "Agreement theorems for high dimensional expanders in the small soundness regime: the role of covers", arXiv:2308.09582 (2023), ECCC TR23-119.
- M. Bafna, D. Minzer, "Characterizing direct product testing via coboundary expansion", STOC (2024), arXiv:2308.09668.
