# Emptiness of tree automata with arbitrary equality constraints is undecidable

When the transitions of a bottom-up tree automaton may test equality or disequality of arbitrary subterms of the current node, no algorithm decides whether the automaton accepts any tree; restricting the tests to direct subterms (siblings) restores decidability.

A *tree automaton with equality and disequality constraints* (AWEDC) over a ranked alphabet is a nondeterministic bottom-up [tree automaton](../../../omega-automata-and-games/logic-and-tree-automata/bottom-up-finite-tree-automata.md) whose transitions are guarded by Boolean combinations of tests $t|_p=t|_{p'}$ and $t|_p\ne t|_{p'}$, comparing the subterms of the current term $t$ at positions $p,p'$, which may lie arbitrarily deep below the node.

**Theorem.** Emptiness of tree automata with arbitrary equality and disequality constraints between subterms is undecidable.

Emptiness becomes decidable under restrictions: for constraints between direct subterms, i.e. siblings (Bogaert and Tison), also in the unranked setting with MSO-definable sibling constraints (Karianto and Löding; Löding and Wong), and for reduction automata, which bound the number of equality tests along each path (Dauchet, Caron and Coquidé; Caron, Comon, Coquidé, Dauchet and Jacquemard).

## Depends on

- [Bottom-up finite tree automata](../../../omega-automata-and-games/logic-and-tree-automata/bottom-up-finite-tree-automata.md)

## Proof depends on

None.

## Expansion

The source read recalls this result from Mongy-Steen's thesis without proof. A good expansion gives the reduction from an undecidable problem, such as Post's correspondence problem or the halting problem of a two-counter machine, encoding solutions or computations as terms whose required equalities between deep subterms are checked by the constraints, and links the page of that problem.

## Sources

- Christof Löding and Karianto Wong, "On Nondeterministic Unranked Tree Automata with Sibling Constraints", in *IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2009)*, LIPIcs 4, 2009, pp. 311–322, doi:[10.4230/LIPIcs.FSTTCS.2009.2328](https://doi.org/10.4230/LIPIcs.FSTTCS.2009.2328); read in the open-access LIPIcs copy at https://drops.dagstuhl.de/opus/volltexte/2009/2328/: Section 1 (introduction, the undecidability of unrestricted equality constraints and the decidable restrictions).
- The undecidability goes back to J. Mongy-Steen, *Transformation de noyaux reconnaissables d'arbres. Forêts RATEG*, PhD thesis, Université de Lille I, 1981, and is presented in H. Comon, M. Dauchet, R. Gilleron, C. Löding, F. Jacquemard, D. Lugiez, S. Tison and M. Tommasi, *Tree Automata Techniques and Applications* (TATA), open-access book, HAL hal-03367725; both cited as recalled in the source above (neither read: the TATA copy on HAL could not be retrieved).
