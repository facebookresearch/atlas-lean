# Origin semantics of transducers and bounded regular resynchronizers

The origin semantics of a transducer records, for each output position, the input position the head was reading when it was produced;
a bounded regular resynchronizer is an MSO formula that redirects origins, each new origin coming from boundedly many old ones, and
induces a containment preorder between transducers.

**Transducers.** A *one-way nondeterministic transducer* (1NT) reads its input from left to right, each transition consuming at most one input
letter and producing an output word. A *two-way nondeterministic transducer* (2NT) has transitions $(p, a, v, d, q)$ with
$a \in \Sigma \cup \{\vdash, \dashv\}$, output $v \in \Gamma^*$ and a direction $d$ of the head (left or right), on the input framed by end markers, which
produce no output. A run outputs the concatenation of the output words of its transitions; the relation $[\![T]\!] \subseteq \Sigma^* \times \Gamma^*$ is
the set of input–output pairs of accepting runs. As in the source, input words are assumed nonempty throughout.

**Origin semantics.** An *origin graph* is a triple $(u, v, \mathrm{orig})$ with $u \in \Sigma^*$, $v \in \Gamma^*$ and $\mathrm{orig}$ mapping each position of
$v$ to a position of $u$. A run of $T$ on $u$ producing $v$ gives the origin graph in which each output position is mapped to the position of the
head when it was written (outputs after the end of the input of a 1NT get the last input position). The *origin semantics* of $T$ is the set of origin
graphs of its accepting runs.

**Resynchronizers.** A *regular* (MSO) *resynchronizer* $R$ with $m$ input parameters is an MSO formula $\gamma(\bar I, x, y)$ over input words, with
monadic parameters $\bar I = (I_1, \dots, I_m)$ and first-order variables $x, y$. It relates origin graphs $(u, v, \mathrm{orig})$ and
$(u, v, \mathrm{orig}')$ with the same input and output if some valuation $\bar I$ of the parameters satisfies $\gamma(\bar I, \mathrm{orig}(z), \mathrm{orig}'(z))$
on $u$ for every output position $z$. It has *bound* $k$ if for every input, every valuation of the parameters and every position $y$, at most $k$
positions $x$ satisfy $\gamma(\bar I, x, y)$; it is *bounded* if it has some bound. For transducers $T_1, T_2$, write $T_1 \subseteq R(T_2)$ if for every origin
graph $\sigma_1$ of $T_1$ some origin graph $\sigma_2$ of $T_2$ is related to it by $R$ in this order, that is, $R$ redirects the origins of $\sigma_2$ (the old origins $x$) to those of $\sigma_1$ (the new origins $y$), and $T_1 \preceq T_2$ if $T_1 \subseteq R(T_2)$ for some bounded regular resynchronizer $R$. The
relation $\preceq$ is a preorder; $T_1 \sim T_2$ means $T_1 \preceq T_2$ and $T_2 \preceq T_1$.

For a fixed bounded resynchronizer $R$, whether $T_1 \subseteq R(T_2)$ is decidable in PSPACE, by earlier work the source cites; without the boundedness
restriction, the resynchronizer relating all graphs with the same input and output makes it classical inclusion, which is undecidable.

## Depends on

- [Rational relations and transducers](../rational-relations-and-transducers.md)
- [Monadic second-order logic over words](../../../../omega-automata-and-games/logic-and-tree-automata/monadic-second-order-logic-over-words.md)

## Proof depends on

None.

## Sources

- D. Kuperberg and J. Martens, "Regular resynchronizability of origin transducers is undecidable", in *45th International Symposium on Mathematical Foundations of Computer Science (MFCS 2020)*, LIPIcs 170, paper 58, 2020, doi:10.4230/LIPIcs.MFCS.2020.58; read in arXiv:2002.07558v3: Section 2 (1NTs, 2NTs and origin semantics), Section 3 (Definition 2 of MSO resynchronizers and their semantics, Definition 7 of containment up to a resynchronizer, Definition 8 of boundedness, and Theorem 9 for a fixed bounded resynchronizer) and the beginning of Section 4 (the relation $\preceq$ and Lemma 11), with the numbering of that version.
