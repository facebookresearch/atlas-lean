# The team DFA game and its communication variant

In the team DFA game, two cooperating players and one adversary feed bits to a deterministic finite automaton; the adversary sees
everything, while each team member sees only one of the adversary's bits per round. The communication variant lets the team members
exchange a bounded number of bits per round according to a fixed periodic policy.

**Team DFA game** (introduced by Coulombe and Lynch in 2018, as the source recalls). An instance is a DFA $D = (\{0, 1\}, Q, q_0, \delta, F_\exists \cup F_\forall)$ over the binary alphabet with disjoint sets
$F_\exists$ and $F_\forall$ of winning states for the existential team $\{\exists_0, \exists_1\}$ and for the universal player $\forall$. Starting in
$q_0$, each round proceeds as follows: if the current state is in $F_\exists$ the existential team wins, and if it is in $F_\forall$ the universal
player wins; otherwise $\forall$, who knows the state, inputs two bits $b_0, b_1$ to $D$; then $\exists_0$, knowing $b_0$, inputs a bit $m_0$, and
$\exists_1$, knowing $b_1$, inputs a bit $m_1$; $\forall$ learns $m_0$ and $m_1$. Each team member chooses moves from the information it has
learned so far, and neither sees the other's moves. A team has a *forced win* if its members have strategies that guarantee that
the team wins; a play that never reaches $F_\exists \cup F_\forall$ is not a win for the existential team. The question is whether the
existential team has a forced win.

**Communication.** A *policy* $P$ consists of a DFA over the one-letter alphabet with states $\Pi$, start state $p_0$ and transition
$\pi$, together with maps $P_{\mathrm{mid}}, P_{\mathrm{end}} : \Pi \to \mathbb{N} \times \mathbb{N}$. In the *team DFA game with communication*
(TDGC) on $(D, P)$, a round in policy state $p$ is a round of the team DFA game in which, after $\exists_0$ and $\exists_1$ learn $b_0$ and $b_1$
and before they move, they simultaneously exchange messages of $P_{\mathrm{mid}}(p) = (n_{01}, n_{10})$ bits ($n_{01}$ bits from $\exists_0$ to
$\exists_1$ and $n_{10}$ from $\exists_1$ to $\exists_0$), which $\forall$ also learns; after the moves they exchange messages of $P_{\mathrm{end}}(p)$ bits
in the same way; then the policy moves to $\pi(p)$. A policy is *$(r, x_0, x_1, N)$-rate-limited* if after the first $N$ rounds, in each
block of $r$ consecutive rounds starting at round $N + \ell r$ with $\ell \in \mathbb{N}$, the total number of bits sent from $\exists_i$ to
$\exists_{1-i}$, mid-round and end-round together, is exactly $x_i$.

Since the policy DFA reads a single letter, its state sequence is an initial chain followed by a cycle, so the bandwidth of every
round is fixed in advance.

## Depends on

None.

## Proof depends on

None.

## Sources

- M. Coulombe and J. Lynch, "Characterizing the decidability of finite state automata team games with communication", in *Proceedings of the 13th International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2022)*, Electronic Proceedings in Theoretical Computer Science 370, pp. 213–228, 2022, doi:10.4204/EPTCS.370.14; read in arXiv:2209.10324v1: Definition 1 in Section 1.1 (the team DFA game), Definition 2 and the communication model in Section 1.2 (the team DFA game with communication), and Definition 3 (rate-limited policies) in Section 3.
