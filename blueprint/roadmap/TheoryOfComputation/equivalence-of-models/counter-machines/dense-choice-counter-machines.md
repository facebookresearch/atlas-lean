# Dense-choice counter machines

A dense-choice counter machine is a counter machine whose counters hold nonnegative reals and can be changed by $1$ or by a
nondeterministically chosen real $\delta \in (0, 1)$, fixed anew at each step; guards test counters against $0$ or, for $k$-testable
counters, against integers up to $k$.

**Machines.** Let $x_1, \dots, x_n$ be *dense-choice counters* with values in $\mathbb{R}_{\ge 0}$, let $G = \{(x = 0), (x > 0), \mathit{true}\}$ be the
set of guards and $A = \{1, \Delta\}$ the set of actions. A *dense-choice counter machine* (DCM) with $n > 0$ counters is a pair
$\mathcal{M} = \langle S, T \rangle$ of a finite set $S$ of control states, with a designated final state $s_{\mathrm{fin}}$, and a finite set of transitions
$T \subseteq S \times (G \times \mathbb{Z} \times A)^n \times S$. Configurations are pairs $(s, \mathbf{x}) \in S \times \mathbb{R}_{\ge 0}^n$, and a transition
$(s, (\mathbf{g}, \boldsymbol{\lambda}, \mathbf{a}), s')$ leads from $(s, \mathbf{x})$ to $(s', \mathbf{x}')$ if for some $\delta$ with $0 < \delta < 1$ the valuation
$\mathbf{x}$ satisfies the guards $\mathbf{g}$ and

$$
\mathbf{x}' = \mathbf{x} + \boldsymbol{\lambda} \mathbf{u}, \qquad u_i = 1 \text{ if } a_i = 1, \quad u_i = \delta \text{ if } a_i = \Delta ,
$$

where the new valuation must again be nonnegative, so a machine *crashes* when it tries to decrease a counter below $0$. The same $\delta$ is
used for all counters in one step, and a new $\delta$ is chosen at each step.

**Variants.** A counter is *purely dense-choice* if its action is $\Delta$ in every transition, and a *purely-DCM* has only purely dense-choice
counters; a DCM whose actions are all $1$ is an ordinary counter machine. For $k \in \mathbb{N}$, a *$k$-DCM* may use the guards $(x = i)$, $(x < i)$,
$(x > i)$ and $\mathit{true}$ for $i \in [0, k]$, and its counters are called *$k$-testable*. A counter is *$b$-bounded* if its value stays at most $b$
along every run, and *bounded* if it is $b$-bounded for some $b$.

**Problems.** A *run* is a finite sequence of transitions $(s_0, \mathbf{x}_0) \to \cdots \to (s_l, \mathbf{x}_l)$, $l \ge 0$; it is *accepting* if it ends in the final state $s_{\mathrm{fin}}$, whatever configuration it starts from. The *state reachability problem* asks, for a DCM (a finite object, its transitions carrying integer coefficients) and a control state $s$, whether $s$ occurs on some accepting run. No initial configuration is part of the input.

## Depends on

None.

## Proof depends on

None.

## Sources

- F. Bouchy, A. Finkel and P. San Pietro, "Dense-choice counter machines revisited", in *Proceedings of the International Workshop on Verification of Infinite-State Systems (INFINITY 2009)*, Electronic Proceedings in Theoretical Computer Science 10, pp. 3–22, 2009, doi:10.4204/EPTCS.10.1; journal version *Theoretical Computer Science* 542:17–31, 2014, doi:10.1016/j.tcs.2014.04.029. Read in arXiv:0911.3405v1: Definitions 2.4 and 2.5 in Section 2.2 (DCMs and their semantics, the state reachability problem), the definition of $k$-DCMs in Section 2.2, Definition 2.7 (purely dense-choice counters), and the definition of bounded counters at the start of Section 3.1.
