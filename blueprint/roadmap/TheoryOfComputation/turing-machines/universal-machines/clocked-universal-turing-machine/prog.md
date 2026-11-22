# The clocked universal program

The program of the clocked universal machine gives an
instruction for every label. Numbers sit on stacks as counters of units (the bit true), and a cell
is a counter followed by a marker (the bit false).

Tape update. $\mathsf{act0}$ empties $Q$ and $\mathsf{act1}$ moves the counter $N$ onto $Q$.
$\mathsf{act2}$ pops $A$ and goes to $\mathsf{mvL0}$ if $A$ was empty, else to $\mathsf{act3}$,
which pops $A$ and goes to $\mathsf{mvR0}$ if $A$ was empty, else to $\mathsf{wr0}$; so the action
$0$ moves left, $1$ moves right and $a + 2$ writes $a$. $\mathsf{wr0}$ empties $H$ and
$\mathsf{wr1}$ moves the counter $A$ onto $H$. A left move ($\mathsf{mvL0}$ to $\mathsf{mvL3}$)
pushes a marker on $R$, moves the units of $H$ onto $R$, moves the units on top of $L$ onto $H$
and pops one more symbol of $L$; a right move ($\mathsf{mvR0}$ to $\mathsf{mvR3}$) does the same
with $L$ and $R$ exchanged. Writes and moves end at $\mathsf{fin}$, which pops the clock $Ck$ and
goes to $\mathsf{tmo}$ if it was empty, else to $\mathsf{sc0}$.

Scan. $\mathsf{sc0}$ goes to $\mathsf{nf}$ if $C$ is empty, else to $\mathsf{rq0}$. Then
$\mathsf{rq0}$, $\mathsf{rq1}$ move the units on top of $C$ onto $T$ and pop the next symbol of
$C$; $\mathsf{rq2}$ compares $T$ with $Q$ unit by unit, parking the popped units on $U$ and $V$;
$\mathsf{cqA}$, $\mathsf{cqB}$ move $U$ back onto $T$ and $V$ back onto $Q$; $\mathsf{sq0}$,
$\mathsf{sq1}$ move $T$ onto $B$, push a marker on $B$, and go to $\mathsf{ra0}$ if the two
counters were equal, else to $\mathsf{sk3a}$. The labels $\mathsf{ra0}$ to $\mathsf{sa1}$ do the
same with $H$ in place of $Q$, and go to $\mathsf{rd0}$ on equality, else to $\mathsf{sk2a}$.
From $\mathsf{sk3a}$, $\mathsf{sk2a}$ or $\mathsf{sk1a}$ the program moves three, two or one
further cells of $C$ onto $B$ (the units, then the next symbol replaced by a marker) and returns
to $\mathsf{sc0}$. The labels $\mathsf{rd0}$ to $\mathsf{rd3}$ move the units on top of $C$ onto
both $N$ and $B$, pop the next symbol of $C$ and push a marker on $B$; $\mathsf{rd4}$ to
$\mathsf{rd7}$ do the same with $A$ in place of $N$ and go to $\mathsf{rs}$. Finally
$\mathsf{rs}$ and $\mathsf{nf}$ move all of $B$ back onto $C$, one symbol at a time, and go to
$\mathsf{act0}$ and $\mathsf{hlt}$ respectively.

Parse. $\mathsf{pc0}$, $\mathsf{pc1}$ move the units on top of $X$ onto $Ck$ and pop the next
symbol of $X$. Then, while the top of $X$ is a unit, $\mathsf{px0}$ to $\mathsf{px2}$ move the
units on top of $X$ onto $P$, pop the next symbol of $X$ and push a marker on $P$; otherwise
$\mathsf{px3}$ pops $X$, $\mathsf{px4}$ moves all of $P$ onto $R$, $\mathsf{px5}$, $\mathsf{px6}$
move the units on top of $R$ onto $H$ and pop the next symbol of $R$, and $\mathsf{pk0}$ moves all
of $X$ onto $C$ and goes to $\mathsf{sc0}$.

Exits. $\mathsf{tmo}$ pushes a marker on $O$ and goes to $\mathsf{done}$. $\mathsf{hlt}$ pushes a
marker on $R$, $\mathsf{o1}$ moves the units of $H$ onto $R$, $\mathsf{o2}$ moves all of $R$ onto
$P$, $\mathsf{o3}$ pops the markers on top of $P$, $\mathsf{o4}$ pushes one marker on $P$ unless
$P$ is empty, $\mathsf{o5}$ moves all of $P$ onto $O$, and $\mathsf{o6}$ pushes a unit on $O$ and
goes to $\mathsf{done}$, where the program halts.
