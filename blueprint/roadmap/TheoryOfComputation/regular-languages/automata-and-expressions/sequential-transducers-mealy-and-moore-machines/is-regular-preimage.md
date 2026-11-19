# Inverse sequential transduction preserves regular languages

Let $S$ be a sequential
transducer with finitely many states, input alphabet $I$ and output alphabet $O$, and let $L$ be
a regular language over $O$. Then the preimage of $L$ under $S$, the set of words over $I$ that
$S$ translates to some word of $L$, is regular.

The proof is the product of $S$ with a DFA for $L$, started in the DFA state reached on the
initial output of $S$.
