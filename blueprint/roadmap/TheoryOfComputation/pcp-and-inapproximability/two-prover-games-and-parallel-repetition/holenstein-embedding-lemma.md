# Holenstein's embedding lemma for conditioned repetitions

Fix strategies for $G^n$ and a set $C \subseteq [n]$ of coordinates, and let $W_C$ be the event that every coordinate in $C$ is won. Then for each free coordinate $j \notin C$ there is an error $\varepsilon_j \ge 0$ such that Alice and Bob, without communication but with shared randomness, can jointly sample from a distribution within statistical distance $\varepsilon_j$ of the law of the full questions conditioned on $W_C$ and on $(x_j, y_j) = (x, y)$, given only $x$ and $y$ respectively with $(x,y) \sim \mu$, and (Holenstein 2009, Lemma 6.4)

$$\sum_{j \notin C} \varepsilon_j \le 15 \sqrt{|C^c| \Big(|C| \log_2(|A||B|) + \log_2 \frac{1}{\Pr[W_C]}\Big)}.$$

## Proof sketch

Conditioning a product distribution on an event of probability $p$ changes the joint law of the coordinates by a total KL divergence at most $\ln(1/p)$ plus the entropy of the answers in $C$; Pinsker's inequality distributes this over the free coordinates, and correlated sampling lets the two players reproduce the conditioned distributions with error controlled by these divergences.

## Depends on

- [Parallel repetition of a two-prover game](parallel-repetition-of-a-game.md)

## Sources

- T. Holenstein, "Parallel Repetition: Simplifications and the No-Signaling Case", Theory of Computing 5, 2009.
