# MSO-definable languages are regular

Over a finite alphabet $\Sigma$, view a nonempty word $w = a_0 \cdots a_{n-1}$ as the structure with domain $\{0, \dots, n-1\}$, the successor relation, the order $<$ and a unary predicate $P_a$ for each letter $a$. A language of nonempty words is definable by a sentence of monadic second-order logic over these structures if and only if it is regular (the Büchi–Elgot–Trakhtenbrot theorem). From an automaton one writes an existential monadic sentence whose set variables guess the run; from a sentence one builds an automaton by induction, using closure of regular languages under Boolean operations and under projection of an extended alphabet for set quantifiers. The construction from sentences has nonelementary worst-case size.

## Expansion

This page becomes ready once these prerequisites are stated:

- The syntax and semantics of monadic second-order logic over finite words (statement prerequisite)
- Closure of the regular languages under union, complementation and projection, with the automaton constructions the translation uses (proof prerequisite)

## Sources

- *Logic*, lecture 21 notes, Chennai Mathematical Institute, 3 November 2015, the Büchi–Elgot–Trakhtenbrot theorem with both directions of its proof and the complexity remark, <https://www.cmi.ac.in/~madhavan/courses/logic2015/lectures/lecture21-03nov2015.txt>
- W. Thomas, *Applied Automata Theory*, lecture notes, RWTH Aachen University, Chapters 0 and 1
