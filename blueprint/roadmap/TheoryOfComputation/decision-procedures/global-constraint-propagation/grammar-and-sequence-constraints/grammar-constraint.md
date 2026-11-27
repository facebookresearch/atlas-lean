# GRAMMAR and REGULAR constraints

The GRAMMAR constraint requires the values of a sequence of $n\ge1$ variables, read in order, to form a word of a given context-free language; REGULAR is the special case of a regular language given by a deterministic finite automaton or a regular grammar.

Let $G=\langle T,H,P,S\rangle$ be a context-free grammar with terminals $T$, nonterminals $H$, productions $P$ and start symbol $S$, with language $L(G)$ ([words derivable from $S$](../../../context-free-languages/grammars-and-pushdown-automata/context-free-grammars/mem-language-iff-yields.md)). Let $n\ge1$ and let $X_1,\dots,X_n$ be distinct variables whose domains $D(X_i)$ are finite subsets of $T$.

- $\mathrm{GRAMMAR}(G,[X_1,\dots,X_n])$ (also written $\mathrm{CFG}$) allows exactly the assignments $(a_1,\dots,a_n)$ with $a_1a_2\cdots a_n\in L(G)$.
- The **Cartesian product language** of the domains is $L(R_{D(X_1),\dots,D(X_n)})=\{a_1\cdots a_n: a_i\in D(X_i)\}$. The constraint has an allowed assignment iff $L(G)\cap L(R_{D(X_1),\dots,D(X_n)})\ne\emptyset$; because $n\ge1$, this is also the condition for some value to have a support.
- A **deterministic finite automaton** $M=(Q,T,\delta,q_0,F)$ has finite states $Q$, a partial transition function $\delta:Q\times T\to Q$, a start state $q_0$ and accepting states $F\subseteq Q$; it accepts a word when the run from $q_0$ reading it is defined and ends in $F$. $\mathrm{REGULAR}(M,[X_1,\dots,X_n])$ allows the assignments whose word $M$ accepts.
- A grammar is **regular** (right-linear) when all its productions have the forms $A\to aB$ or $A\to a$ ($a\in T$, $A,B\in H$); such a grammar has no empty productions and does not generate the empty word.

Size conventions differ between sources and matter for running times: Quimper and Walsh measure $|G|$ by the number of productions of a grammar in Chomsky normal form; Katsirelos, Maneth, Narodytska and Walsh use $|G|=\sum_{A\to\alpha\in P}|A\alpha|$ for grammars without empty productions; the size of an automaton is measured by the number $|\delta|$ of defined transitions. A DFA gives a regular grammar with one production $q\to aq'$ per transition $\delta(q,a)=q'$ and one production $q\to a$ per transition into an accepting state, generating exactly the nonempty words the DFA accepts, so REGULAR on $n\ge1$ variables is GRAMMAR for a regular grammar of size $O(|\delta|)$.

## Depends on

- [Language membership through yields](../../../context-free-languages/grammars-and-pushdown-automata/context-free-grammars/mem-language-iff-yields.md): the language of a context-free grammar.

## Proof depends on

None.

## Expansion

The support statement is immediate: an allowed assignment is a word of $L(G)$ whose $i$-th letter lies in $D(X_i)$, i.e. a word of the intersection (Proposition 1 of Katsirelos et al.), and with $n\ge1$ any allowed assignment supports its own values. For $n=0$ the definitions would diverge: an automaton accepting the empty word gives a solution but no variable has a value to support, and a regular grammar cannot generate the empty word; the convention $n\ge1$ excludes this case. The regular grammar of a DFA generates a word $a_1\cdots a_m$, $m\ge1$, from $q_0$ iff the run on it ends in an accepting state, by induction on $m$.

Pesant introduced REGULAR with a domain consistency propagator based on unfolding the automaton into $n$ layers; Quimper and Walsh, and independently Sellmann, introduced GRAMMAR with a propagator based on the CYK parser.

## Sources

- C.-G. Quimper and T. Walsh, "Decomposing global grammar constraints", *Principles and Practice of Constraint Programming – CP 2007*, Lecture Notes in Computer Science 4741 (2007), 590–604, doi:10.1007/978-3-540-74970-7_42. §2 (grammars in Chomsky normal form, GRAMMAR, REGULAR as a special case, regular productions), pp. 591–592.
- G. Katsirelos, S. Maneth, N. Narodytska and T. Walsh, "Restricted global grammar constraints", *Principles and Practice of Constraint Programming – CP 2009*, Lecture Notes in Computer Science 5732 (2009), 501–508, doi:10.1007/978-3-642-04244-7_40. Background (grammar size, regular grammars), Definition 1, Cartesian product languages and Proposition 1, §§2–3 of arXiv:0906.5233v1, [https://arxiv.org/abs/0906.5233v1](https://arxiv.org/abs/0906.5233v1).
- W.-J. van Hoeve and I. Katriel, "Global constraints", in F. Rossi, P. van Beek and T. Walsh (eds.), *Handbook of Constraint Programming*, Elsevier (2006), chapter 6, 169–208, doi:10.1016/S1574-6526(06)80010-6; author copy [https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf](https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf). Definition 3 (regular language membership constraint for a DFA) in §7.2.7 (section numbers of the author copy).
