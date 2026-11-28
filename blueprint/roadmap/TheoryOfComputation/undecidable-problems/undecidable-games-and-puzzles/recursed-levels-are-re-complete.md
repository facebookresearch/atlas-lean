# Deciding whether a level of Recursed can be solved is RE-complete

Deciding whether the player can reach the goal crystal in a given level of the puzzle platform video game Recursed, whose treasure chests open rooms like function calls, is RE-complete, so the problem is undecidable.

**Setting.** A level of Recursed consists of finitely many rooms of size at most $15\times20$ built from tiles, together with objects (blocks, keys and locked doors, treasure chests, green flames, jars and cauldrons, ledges). The player character can run, jump at most three tiles high, fall, and carry, drop or throw one object at a time. Jumping into a treasure chest enters the room it contains, a new copy of that room, and leaving the room returns the player to the room containing the chest, possibly carrying an object; a green flame can create a jar that later returns to the room where it was created, in the state the player left it, and each jar can be entered once. The goal of a level is to reach its single purple crystal.

**Theorem (Demaine, Kopinsky and Lynch).** It is RE-complete to decide whether a player can reach the crystal in a given level of Recursed (Theorem 3.1).

Membership in RE holds because the game can be simulated from an initial state and a sequence of inputs, so all input sequences can be enumerated. The levels produced by the reduction obey the constraints of the levels of the main game, including the room size, and a Turing machine can be simulated by a level of size linear in its description with a solution of length polynomial in its running time. The source conjectures that Recursed with cauldrons but no jars is still undecidable.

## Depends on

- [Recognizability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

A good expansion adds and links definition pages for the model the statement quantifies over, as Section 2 of the source fixes it: levels (rooms, tiles and objects), the player's moves, the semantics of treasure chests, green flames, jars and cauldrons, and the goal of reaching the crystal.

The hardness proof reduces the Post correspondence problem, with a prescribed first domino, by implementing a nondeterministic algorithm: repeatedly choose a domino and push its top half onto a stack $S_A$ and its bottom half onto a stack $S_B$, then pop both stacks symbol by symbol and check that they agree and empty together. In the level, $S_A$ is the call stack of rooms entered through chests and $S_B$ is a chain of nested jars that the player carries. In the pushing phase the player selects dominoes and adds the corresponding rooms and jars; in the checking phase the player climbs back up the chests, performing for each pair of top symbols a handshake between the matching rooms of the two stacks, and gets stuck if the symbols differ. A global-lock gadget, one-time-traversal gadgets and prove and verify gadgets enforce the intended order (Lemmas 3.2 and 3.3). Only when both stacks are emptied together does the player return to the start room carrying the initial block, which is needed to jump up to the crystal; so the crystal is reachable exactly when the instance has a solution.

## Sources

- Erik D. Demaine, Justin Kopinsky and Jayson Lynch, "Recursed is not recursive: a jarring result", in *31st International Symposium on Algorithms and Computation (ISAAC 2020)*, Leibniz International Proceedings in Informatics 181, paper 50, pp. 50:1–50:15, 2020, doi:[10.4230/LIPIcs.ISAAC.2020.50](https://doi.org/10.4230/LIPIcs.ISAAC.2020.50); read in the open-access published version ([PDF](https://drops.dagstuhl.de/storage/00lipics/lipics-vol181-isaac2020/LIPIcs.ISAAC.2020.50/LIPIcs.ISAAC.2020.50.pdf)): the game rules of Section 2, Theorem 3.1 with its proof sketch and Lemmas 3.2 and 3.3 in Section 3, the abstract for the efficiency of the reduction, and Conjecture 1 in Section 4; the full version is arXiv:2002.05131v2.
