# Labels of the clocked universal machine

The label set of the clocked universal program consists of the following pairwise distinct
labels, where $o$ ranges over the three comparison outcomes $<$, $=$, $>$ and $m$ over the two
bits:

- the tape update: $\mathsf{act0}, \dots, \mathsf{act3}$, $\mathsf{wr0}$, $\mathsf{wr1}$,
  $\mathsf{mvL0}, \dots, \mathsf{mvL3}$, $\mathsf{mvR0}, \dots, \mathsf{mvR3}$, and the clock
  tick $\mathsf{fin}$;
- the scan, which starts at $\mathsf{sc0}$: for the state, $\mathsf{rq0}$, $\mathsf{rq1}$,
  $\mathsf{rq2}$, $\mathsf{cqA}(o)$, $\mathsf{cqB}(o)$, $\mathsf{sq0}(m)$, $\mathsf{sq1}(m)$; for
  the head cell, $\mathsf{ra0}$, $\mathsf{ra1}$, $\mathsf{ra2}$, $\mathsf{caA}(o)$,
  $\mathsf{caB}(o)$, $\mathsf{sa0}(m)$, $\mathsf{sa1}(m)$; for skipping the rest of an entry,
  $\mathsf{sk3a}$, $\mathsf{sk3b}$, $\mathsf{sk2a}$, $\mathsf{sk2b}$, $\mathsf{sk1a}$,
  $\mathsf{sk1b}$; and for reading a matching entry, $\mathsf{rd0}, \dots, \mathsf{rd7}$;
- the restores $\mathsf{rs}$ and $\mathsf{nf}$, and the exits $\mathsf{hlt}$ and $\mathsf{tmo}$;
- the parse of the encoded input: $\mathsf{pc0}$, $\mathsf{pc1}$, $\mathsf{px0}, \dots, \mathsf{px6}$, $\mathsf{pk0}$;
- the output phase: $\mathsf{o1}, \dots, \mathsf{o6}$ and $\mathsf{done}$.

In particular there are finitely many labels ($77$).
