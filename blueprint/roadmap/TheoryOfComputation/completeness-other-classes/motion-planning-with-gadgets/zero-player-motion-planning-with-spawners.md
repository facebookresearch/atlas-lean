# Zero-player motion planning with robot spawners is RE-complete

When gadgets are traversed by deterministically moving robots and a spawner gadget creates a new robot in every round, deciding whether some robot ever reaches a target location is RE-complete, hence undecidable, already for four specific gadgets.

**Model.** Gadgets are as in [gadgets and motion-planning games](gadgets-and-motion-planning-games.md). In *0-player directed-edge motion planning* the connection graph between gadget locations is directed, each location has only incoming edges or at most one outgoing edge, and all gadgets are deterministic, so a robot moves on its own along the edge it is on and traverses the gadgets it meets. A *spawner* is a one-location gadget that creates a new robot at its location in every round. *0-player directed-edge motion planning with spawners* proceeds in rounds: in each round every robot, in spawn order, moves along its directed edge until it traverses one gadget or gets stuck, and then every spawner creates a robot. The *robot reachability* problem asks, given such a system (finitely many gadgets from the given set, with their initial states and initial robots, the directed connection graph and the spawners) and a target location, whether some robot reaches the target in finite time.

The four gadgets of the theorem are the *increment gadget* (four states, ten locations: a three-path path selector that, when traversed, enables one path of a three-path lock branch and locks itself, the gadget returning to its initial state when a lock-branch path is traversed), the *register gadget* (three states, ten locations: a path selector, a processing branch and a response branch), the *UPDSDS gadget* (two states up and down, a tunnel setting the state to up and two switches, each with one input and two outputs, whose output depends on the state and which set the state to down), and the spawner.

**Theorem (Ani, Coulombe, Demaine, Diomidov, Gomez, Hendrickson and Lynch).** Robot reachability for 0-player directed-edge motion planning with spawners is in RE for every set of gadgets (Lemma 3.1), and it is RE-hard with the spawner, increment, register and UPDSDS gadgets combined (Theorem 3.2). Hence it is RE-complete, and undecidable, for these four gadgets.

Without spawners, the 0-player problem with a single robot is in PSPACE, since a configuration is described by the gadget states and the robot's position. In the 1-player version, where the player chooses the robots' moves, robot reachability with symmetric self-closing doors and a spawner (optionally a destroyer) is EXPSPACE-complete, by an equivalence with Petri-net coverage (Theorem 4.6 of the source).

## Proof sketch

Membership in RE: after each round the number of robots is finite, so the system can be simulated round by round until a robot reaches the target. Hardness reduces the halting problem of counter machines with three counters and instructions increment, decrement and jump-if-zero, which is undecidable. Each counter is a register gadget whose value is the number of robots stuck at the entrance of its processing branch: a robot passing the decrement path lets one stored robot through to a sink, and if no robot is stored the robot leaves by the other response path, which implements the zero test. Spawners supply fresh robots, and the increment gadget routes one of them into a register to add one to its value. Each instruction of the machine becomes a module of gadgets with execute, pass and jump entrances and exits, built from these gadgets and the UPDSDS gadget, and the halting instruction leads to the target. So some robot reaches the target exactly when the machine halts. Counter machines with three counters halt undecidably because two-counter machines are already universal.

## Depends on

- [Gadgets and motion-planning games](gadgets-and-motion-planning-games.md)
- [Recognizability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Sources

- Joshua Ani, Michael Coulombe, Erik D. Demaine, Yevhenii Diomidov, Timothy Gomez, Dylan Hendrickson and Jayson Lynch, "Complexity of motion planning of arbitrarily many robots: gadgets, Petri nets, and counter machines", in *2nd Symposium on Algorithmic Foundations of Dynamic Networks (SAND 2023)*, Leibniz International Proceedings in Informatics 257, paper 5, pp. 5:1–5:21, 2023, doi:[10.4230/LIPIcs.SAND.2023.5](https://doi.org/10.4230/LIPIcs.SAND.2023.5); read in arXiv:2306.01193v1 ([arXiv](https://arxiv.org/abs/2306.01193v1)), whose numbering is used: the model and the spawner gadget in Section 3.1, Lemma 3.1 (membership in RE), the increment, register and UPDSDS gadgets and Theorem 3.2 (RE-hardness) with its proof, and Theorem 4.6 for the 1-player result.
