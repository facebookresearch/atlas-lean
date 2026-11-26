# Reachability with directed symmetric self-closing doors is PSPACE-complete

A **directed symmetric self-closing door** is a gadget with an opening traversal and a closing traversal: an agent passing through the opening path opens the door, and traversing the door's main path is possible only when open and closes it again. For a finite network of such doors joined by free connections, with prescribed initial door states, deciding whether a single agent can reach a target location is $\mathsf{PSPACE}$-complete (with no planarity restriction).

## Proof sketch

Membership: door states form a polynomial-size configuration, so reachability is in NPSPACE = PSPACE. Hardness: simulate NCL (or register programs compiled from polynomial-space machines) by building AND and OR behaviour from doors and routing the agent through gadgets that check and update edge orientations.

## Depends on

- [Polynomial space for decision problems](../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Hearn–Demaine: AND/OR constraint-logic reachability is PSPACE-complete](and-or-ncl-pspace-complete.md)
- [Savitch's theorem: NPSPACE = PSPACE](../../complexity-classes/savitch.md)

## Sources

- Joshua Ani et al., "Walking Through Doors Is Hard, Even Without Staircases: Proving PSPACE-Hardness via Planar Assemblies of Door Gadgets", 10th International Conference on Fun with Algorithms (FUN 2021), 2020, Corollary 2.4.
