# Realizability of specifications over infinite words

Let $I$ and $O$ be finite sets of input and output propositions and $\Phi \subseteq (2^I \times 2^O)^\omega$ a specification. A *strategy* is a function $f : (2^I)^+ \to 2^O$; its outcome on an input word $x_0 x_1 \cdots$ is $(x_0, f(x_0))(x_1, f(x_0 x_1)) \cdots$. $\Phi$ is *realizable* if some strategy has all its outcomes in $\Phi$, and *finite-state realizable* if some strategy computed by a finite-state Mealy transducer does. In a common variant the output at each step may depend only on the earlier inputs, so that a strategy is a function $(2^I)^* \to 2^O$.

## Sources

- A. Pnueli and R. Rosner, "On the synthesis of a reactive module", *Proceedings of the 16th ACM POPL*, 1989
- R. Bloem, B. Jobstmann, N. Piterman, A. Pnueli and Y. Sa'ar, "Synthesis of Reactive(1) designs", *Journal of Computer and System Sciences* 78(3):911–938, 2012, Sections 2.3 and 2.3.1 (designs as Mealy machines reading the current input; realizability), <https://www.cse.chalmers.se/~piterman/publications/2012/BJPPS12.pdf>
- O. Kupferman and M. Y. Vardi, "Synthesizing distributed systems", *Proceedings of the 16th IEEE LICS*, 2001, Section 1 (strategies on earlier inputs only, the variant above), <https://www.cs.rice.edu/~vardi/papers/lics01.pdf>
- W. Thomas, "Church's problem and a tour through automata theory", in *Pillars of Computer Science*, LNCS 4800, Springer, 2008
