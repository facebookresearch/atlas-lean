# The team DFA game stays undecidable under rate-limited communication below one bit per round

Letting the two team members of the team DFA game exchange bits does not restore decidability as long as, in the long run, each of
them sends fewer bits than there are rounds.

**Theorem.** For every $(r, x_0, x_1, N)$-rate-limited policy $P$ with $x_0 < r$ and $x_1 < r$, in the sense of the
[team DFA game with communication](the-team-dfa-game-and-its-communication-variant.md), it is undecidable, given a DFA $D$, whether
the existential team has a forced win in the team DFA game with communication on $(D, P)$.

The policy is fixed and the game automaton $D$ is the input. The bound is tight in the following sense: with a one-bit mid-round
exchange every round in both directions, or from $\exists_0$ to $\exists_1$ only, the problem is decidable (in PSPACE and EXPSPACE
respectively). The source proves the analogous statement for the team formula game with communication.

## Depends on

- [The team DFA game and its communication variant](the-team-dfa-game-and-its-communication-variant.md)

## Proof depends on

- [The team DFA game is undecidable](the-team-dfa-game-is-undecidable.md)

## Expansion

The proof reduces the team DFA game without communication. From $D$ it builds a DFA $D'$ that simulates the game on $D$ while
*clogging* the channel: after the first $N$ rounds, the adversary hands each team member private clogging bits that the other member
must later submit to $D'$ for validation, on pain of losing. In a build-up phase of $r^2$ rounds the queues of clogging bits grow, and
since each member can transmit only $x_i < r$ bits per $r$ rounds, the honest strategy of forwarding clogging bits as soon as possible
uses the whole bandwidth. So no useful information passes between the team members, and the team has a forced win on $D'$ exactly
when it has one on $D$. The automaton $D'$ needs only finite memory, about $\max\{\log N, r^2 + \log |Q|, r^3\}$ bits.

## Sources

- M. Coulombe and J. Lynch, "Characterizing the decidability of finite state automata team games with communication", in *Proceedings of the 13th International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2022)*, Electronic Proceedings in Theoretical Computer Science 370, pp. 213–228, 2022, doi:10.4204/EPTCS.370.14; read in arXiv:2209.10324v1: the main theorem of the section "Undecidability of General Communication Games" with its proof (construction outline, build-up, clogging and tear-down phases), the two decidability theorems of the section "Decidability", and the theorem on the team formula game with communication.
