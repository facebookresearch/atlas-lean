# Realizing a parity specification by a transducer

Let $(q_0, \delta, \Omega)$ be a deterministic parity specification over states $Q$, inputs $I$ and outputs $O$, and let $T : I^* \to O$ be a transducer, an arbitrary function from finite input words to output letters. Then $T$ realizes the specification if for every input word $w : \mathbb{N} \to I$, with output word

$$o(k) = T\bigl(w(0), w(1), \dots, w(k)\bigr) \qquad (k \in \mathbb{N}),$$

the priority sequence $\Omega(\rho(0)), \Omega(\rho(1)), \dots$ of the run $\rho$ of the specification on $(w, o)$ satisfies the even max-parity condition: there is an even $d$ that occurs infinitely often in the sequence and is the largest value occurring infinitely often.

The output at time $k$ depends on the first $k + 1$ input letters, the current one included: the environment reveals input letter $k$ before the controller chooses output letter $k$.
