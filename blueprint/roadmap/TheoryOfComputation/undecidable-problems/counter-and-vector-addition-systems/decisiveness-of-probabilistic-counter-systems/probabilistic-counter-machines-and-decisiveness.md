# Probabilistic counter machines and decisiveness

A probabilistic counter machine is a counter machine whose enabled transitions fire with probabilities proportional to weights that may
depend on the counter values; it is decisive with respect to a target set if almost every run reaches the target or a configuration from
which the target is unreachable.

**Markov chains and decisiveness.** A *Markov chain* $\mathcal{M} = (S, p)$ has a countable set $S$ of states and a transition function $p$ from $S$ to
probability distributions on $S$. It is *decisive* with respect to a state $s_0$ and a set $A \subseteq S$ if

$$
\mathbb{P}_{\mathcal{M}, s_0}\bigl(\mathbf{G}(\overline{A} \cap \mathbf{EF} A)\bigr) = 0 ,
$$

that is, almost surely the random path from $s_0$ reaches $A$ or a state from which $A$ cannot be reached. For decisive chains with decidable
reachability, the probability of reaching $A$ can be approximated to any precision by exploring the chain.

**Probabilistic counter machines.** A *probabilistic counter machine* (pCM) $\mathcal{C} = (Q, P, \Delta, W)$ has a finite set $Q$ of control states, counters
$P = \{p_1, \dots, p_d\}$, transitions $\Delta = \Delta_0 \uplus \Delta_1$ and a computable weight function $W : \Delta \times \mathbb{N}^d \to \mathbb{N}_{>0}$. A *zero-test*
transition $(q, p_t, \mathbf{Post}(t), q') \in \Delta_0$ is enabled in configuration $(q, \mathbf{m})$ if $\mathbf{m}(p_t) = 0$ and leads to $(q', \mathbf{m} + \mathbf{Post}(t))$; a transition
$(q, \mathbf{Pre}(t), \mathbf{Post}(t), q') \in \Delta_1$ is enabled if $\mathbf{m} \ge \mathbf{Pre}(t)$ and leads to $(q', \mathbf{m} - \mathbf{Pre}(t) + \mathbf{Post}(t))$. Its Markov chain has states
$Q \times \mathbb{N}^d$; a configuration with no enabled transition loops with probability $1$, and otherwise each enabled transition $t$ fires with probability
$W(t, \mathbf{m}) / \sum_{t' \text{ enabled}} W(t', \mathbf{m})$. The pCM is *static* if every weight $W(t, \cdot)$ is constant, and *polynomial* if every weight is a polynomial in the
counters with nonnegative coefficients and positive constant term. A one-counter pCM is *safe* if every transition of $\Delta_1$ requires the counter to be
positive and changes it by $-1$, $0$ or $+1$.

The *decisiveness problem* asks, given a pCM, an initial configuration $s_0$ and a target set $A$, whether its Markov chain is decisive with respect to
$s_0$ and $A$.

## Depends on

- [Discrete-time Markov chains](../../../../Logic/temporal-logic/probabilistic-model-checking/discrete-time-markov-chains.md)

## Proof depends on

None.

## Sources

- A. Finkel, S. Haddad and L. Ye, "About decisiveness of dynamic probabilistic models", in *34th International Conference on Concurrency Theory (CONCUR 2023)*, LIPIcs 279, paper 14, 2023, doi:10.4230/LIPIcs.CONCUR.2023.14; read in arXiv:2305.19564v1: the section "Decisive Markov chains" (Markov chains and the definition of decisiveness), the section "Probabilistic counter machines" (the definition of pCMs, their Markov chain, static and polynomial pCMs) and the beginning of the section "Probabilistic safe one-counter machines".
