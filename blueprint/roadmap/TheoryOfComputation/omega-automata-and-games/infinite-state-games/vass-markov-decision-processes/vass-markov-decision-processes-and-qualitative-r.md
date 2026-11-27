# VASS Markov decision processes and qualitative reachability

A VASS Markov decision process is a vector addition system with states whose control states are split between a controller, who chooses
transitions, and a random player, who picks enabled transitions with probabilities proportional to fixed weights; qualitative questions ask
whether a target control state is reached surely, almost surely or with probability arbitrarily close to one.

**MDPs.** A *Markov decision process* $M = (C, C_1, C_P, A, \to, p)$ has a countable set $C$ of configurations partitioned into configurations $C_1$ of Player 1 and
$C_P$ of the probabilistic player, actions $A$, a transition relation $\to \subseteq C \times A \times C$, and probability distributions $p(c)$ on the successors of the
configurations $c \in C_P$ that are not deadlocks. A play is maximal if it is infinite or ends in a deadlock. A strategy of Player 1 maps each finite play ending in a
non-deadlocked configuration of $C_1$ to a successor; for a strategy $\sigma$ and an initial configuration $c_0$, $\mathrm{Out}(M, c_0, \sigma)$ is the set of maximal plays from
$c_0$ that respect $\sigma$, and $\mathbb{P}(M, c_0, \sigma, \cdot)$ the induced probability measure.

**VASS-MDPs.** An $n$-dimensional *vector addition system with states* (VASS) $(Q, T)$ has control states $Q$ and transitions $T \subseteq Q \times \mathbb{Z}^n \times Q$; a
transition $(q, \mathbf{z}, q')$ is enabled in configuration $(q, \mathbf{v}) \in Q \times \mathbb{N}^n$ if $\mathbf{v} + \mathbf{z} \ge \mathbf{0}$, and leads to $(q', \mathbf{v} + \mathbf{z})$. A *VASS-MDP*
$(Q, Q_1, Q_P, T, \tau)$ adds a partition of $Q$ into controller states $Q_1$ and probabilistic states $Q_P$ and positive integer weights $\tau(t)$; in its MDP, from a non-deadlocked
configuration $c$ with state in $Q_P$, each enabled transition $t$ is taken with probability $\tau(t) / \sum_{t' \text{ enabled at } c} \tau(t')$. It is *deadlock free* if its VASS has
no deadlocked configuration. In a *P-VASS-MDP* the transitions of Player 1 do not change the counters; in a *1-VASS-MDP* the probabilistic transitions do not.

**Problems.** For an initial configuration $c_0$ and a target control state $q_F$, let $\Diamond q_F$ be the set of maximal plays visiting a configuration with state $q_F$, and
$\Box\Diamond q_F$ the set of infinite plays visiting one infinitely often. The *sure*, *almost-sure* and *limit-sure reachability problems* ask whether some strategy $\sigma$ has
$\mathrm{Out}(M, c_0, \sigma) \subseteq \Diamond q_F$, whether some $\sigma$ has $\mathbb{P}(M, c_0, \sigma, \Diamond q_F) = 1$, and whether $\sup_\sigma \mathbb{P}(M, c_0, \sigma, \Diamond q_F) = 1$; the
*repeated reachability* versions replace $\Diamond q_F$ by $\Box\Diamond q_F$. Every sure instance is an almost-sure instance, every almost-sure instance is a limit-sure instance, and neither inclusion is an equality.

## Depends on

None.

## Proof depends on

None.

## Sources

- P. A. Abdulla, R. Ciobanu, R. Mayr, A. Sangnier and J. Sproston, "Qualitative analysis of VASS-induced MDPs", in *Foundations of Software Science and Computation Structures (FoSSaCS 2016)*, Lecture Notes in Computer Science 9634, pp. 319–334, Springer, 2016, doi:10.1007/978-3-662-49630-5_19; read in arXiv:1512.08824v2: Section 2 (the definitions of MDPs, VASS, VASS-MDPs, P-VASS-MDPs and 1-VASS-MDPs, and the six qualitative problems).
