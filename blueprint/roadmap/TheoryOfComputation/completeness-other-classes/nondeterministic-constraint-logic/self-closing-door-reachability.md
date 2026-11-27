# Reachability with directed symmetric self-closing doors is PSPACE-complete

A **self-closing door** is a two-state (open/closed) gadget with two traversals: an *opening* tunnel or port, which sets the state to open, and a *self-closing* tunnel, which can be traversed only when the door is open and closes it. In a **symmetric** self-closing door the opening tunnel also closes itself: it can be traversed only when the door is closed and its traversal opens the door, so exactly one of the two tunnels is open at any time and traversing it swaps the state. A door is **directed** when each tunnel can be traversed in one direction only. For a finite network of copies of such a door joined by free connections, with prescribed initial door states, deciding whether a single agent can move from a start location to a target location is $\mathsf{PSPACE}$-complete. The same holds for every other variant of self-closing door (directed, undirected or mixed tunnels; with an open-required or an open-optional opening path), and already for planar networks.

## Proof sketch

Membership: the state of the network is the position of the agent together with one bit per door, so reachability is in $\mathsf{NPSPACE}=\mathsf{PSPACE}$. Hardness: a symmetric self-closing door, with one tunnel chosen as opening tunnel, simulates an open-optional self-closing door; undirected doors simulate diodes and hence directed doors; and the directed open-optional self-closing door, with its opening port and self-closing tunnel duplicated by small subnetworks, simulates the directed open-optional open–close door, for which single-agent reachability is known to be $\mathsf{PSPACE}$-hard. The planar case uses planar versions of these simulations.

## Depends on

- [Polynomial space for decision problems](../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Savitch's theorem: NPSPACE = PSPACE](../../complexity-classes/savitch.md)

## Sources

- Joshua Ani, Jeffrey Bosboom, Erik D. Demaine, Yenhenii Diomidov, Dylan Hendrickson and Jayson Lynch, "Walking Through Doors Is Hard, Even Without Staircases: Proving PSPACE-Hardness via Planar Assemblies of Door Gadgets", 10th International Conference on Fun with Algorithms (FUN 2021), Leibniz International Proceedings in Informatics 157, 2020, Section 2.1, Corollary 2.4 and Theorem 3.2.
