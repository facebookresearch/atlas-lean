# Checked-answer branch weights equal conditional checked-answer probabilities

For a finite-dimensional tensor strategy with local POVMs for a repeated anchored game, and a selected unchecked coordinate, define the branch vector obtained by applying the square roots of the checked-answer effects to the shared state (given the retained question information). Then its squared norm equals the actual conditional probability of the checked answers given the selected question pair and the retained information, at every supported value. Given instead a noisy message and Bob's question, the same identity holds, and for a left message the weight splits into the anchor branch and the ordinary branch with the erasure rate $\alpha/2$.

## Proof sketch

Expand the Born rule for the joint measurement: the checked effects act on different tensor factors than the selected coordinate's questions, so conditioning on retained information commutes with taking the norm of the post-measurement branch.

## Depends on

- [Anchoring a two-prover game](anchoring-a-two-prover-game.md)
- [Entangled strategies and the entangled value of a game](../entangled-strategies-and-entangled-value.md)

## Proof depends on

- [Conditional independence of the noisy reveal in anchored repetition](noisy-reveal-conditional-independence.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2), 2022.
