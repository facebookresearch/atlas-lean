# The CLIQUE emitter machine

The CLIQUE emitter is the multi-stack machine with stacks
$T, O, A, B, D, E, X, C, N$, a Boolean flag and the labels named below. The stack $O$ holds
Booleans and the others hold symbols, among them the bit symbols $\mathrm{bit}(b)$, the literal
symbols $\mathrm{lit}(p)$ and the clause marker $\mathrm{cl}$. Each test sets the flag to its
outcome, a pop that reads a polarity or a bit sets the flag to it, and other pops leave the flag
unchanged. To move the bits of $Y$ to $Z$ and then go to $\lambda$ means: while the top of $Y$ is
a bit symbol, pop it and push it onto $Z$; once $Y$ is empty or its top is another symbol, go to
$\lambda$ (the flag serves as scratch). The instruction at each label is as follows.

At $\mathrm{start}$: test whether $T$ is empty; if so go to $\mathrm{fin}$, else pop $T$, push
$\mathrm{cl}$ onto $D$ and onto $C$, and go to $\mathrm{lits}$. At $\mathrm{lits}$: test whether
the top of $T$ is a literal symbol; if so pop it, reading the polarity $q$ (true exactly for
$\mathrm{lit}(\mathrm{true})$), push $\mathrm{cl}$ onto $N$ and go to $\mathrm{nm}(q)$; else go
to $\mathrm{start}$. At $\mathrm{nm}(p)$: move the bits of $T$ to $A$, then go to
$\mathrm{walk}(p, \mathrm{false})$. At $\mathrm{walk}(p, f)$: test whether $D$ is empty; if so
go to $\mathrm{back}(p)$; else test whether the top of $D$ is $\mathrm{cl}$; if so pop it, push
$\mathrm{cl}$ onto $E$ and go to $\mathrm{walk}(p, \mathrm{true})$; else pop $D$, reading $q$
(true exactly for $\mathrm{lit}(\mathrm{true})$), push $\mathrm{lit}(q)$ onto $E$, and if $f$ go
to $\mathrm{cmp}(p, q)$, else push false onto $O$ and go to $\mathrm{mvN}(p, \mathrm{false})$.
At $\mathrm{cmp}(p, q)$: compare the bits of $A$ and $D$, that is, while both tops are bit
symbols of the same bit, pop both and push that bit symbol onto $X$ and onto $B$; when both bit
blocks end together go to $\mathrm{res}(p, b)$ with $b$ true exactly when $p = q$, and on a
mismatch (different bits, or one block ending first) go to $\mathrm{res}(p, \mathrm{true})$
without popping (the flag serves as scratch). At $\mathrm{res}(p, b)$: push $b$ onto $O$ and go
to $\mathrm{rsA}(p)$. At $\mathrm{rsA}(p)$: move the bits of $X$ to $A$, then go to
$\mathrm{rsD}(p)$. At $\mathrm{rsD}(p)$: move the bits of $B$ to $D$, then go to
$\mathrm{mvN}(p, \mathrm{true})$. At $\mathrm{mvN}(p, f)$: move the bits of $D$ to $E$, then go
to $\mathrm{walk}(p, f)$. At $\mathrm{back}(p)$: test whether $E$ is empty; if so go to
$\mathrm{put}(p)$; else test whether its top is $\mathrm{cl}$; if so pop it and push
$\mathrm{cl}$ onto $D$; else test whether its top is a literal symbol; if so pop it, reading $q$
(true exactly for $\mathrm{lit}(\mathrm{true})$), and push $\mathrm{lit}(q)$ onto $D$; else pop
it, reading $b$ (true exactly for $\mathrm{bit}(\mathrm{true})$), and push $\mathrm{bit}(b)$ onto
$D$; in these three cases stay at $\mathrm{back}(p)$. At $\mathrm{put}(p)$: move the bits of $A$
to $B$, then go to $\mathrm{put2}(p)$. At $\mathrm{put2}(p)$: move the bits of $B$ to $D$, then
go to $\mathrm{put3}(p)$. At $\mathrm{put3}(p)$: push $\mathrm{lit}(p)$ onto $D$ and go to
$\mathrm{lits}$. At $\mathrm{fin}$: push false onto $O$ and go to $\mathrm{finN}$. At
$\mathrm{finN}$: pop $N$, testing whether a symbol was popped; if so push true onto $O$ and stay,
else go to $\mathrm{fin2}$. At $\mathrm{fin2}$: push false onto $O$ and go to $\mathrm{finC}$. At
$\mathrm{finC}$: pop $C$, testing whether a symbol was popped; if so push true onto $O$ and stay,
else go to $\mathrm{done}$. At $\mathrm{done}$: halt.
