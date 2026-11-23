# Labels of the SAT-to-CLIQUE emitter

For bits $p, q, f, b$ the labels are
$\mathsf{start}$, $\mathsf{lits}$, $\mathsf{nm}(p)$, $\mathsf{walk}(p, f)$, $\mathsf{cmp}(p, q)$,
$\mathsf{res}(p, b)$, $\mathsf{rsA}(p)$, $\mathsf{rsD}(p)$, $\mathsf{mvN}(p, f)$,
$\mathsf{back}(p)$, $\mathsf{put}(p)$, $\mathsf{put2}(p)$, $\mathsf{put3}(p)$, $\mathsf{fin}$,
$\mathsf{finN}$, $\mathsf{fin2}$, $\mathsf{finC}$ and $\mathsf{done}$. Here $p$ is the polarity
of the current occurrence. $\mathsf{start}$ begins a clause and $\mathsf{lits}$ pops a literal
marker; $\mathsf{nm}$ moves its name to $A$; $\mathsf{walk}(p, f)$ walks $D$, where $f$ tells
whether a clause marker was passed; $\mathsf{cmp}(p, q)$, $\mathsf{res}$, $\mathsf{rsA}$ and
$\mathsf{rsD}$ compare with an occurrence of polarity $q$, push the bit $b$ and restore;
$\mathsf{mvN}$ moves that occurrence's name to $E$; $\mathsf{back}$ moves $E$ back to $D$;
$\mathsf{put}$, $\mathsf{put2}$ and $\mathsf{put3}$ put the current occurrence on $D$;
$\mathsf{fin}$ to $\mathsf{finC}$ push the instance prefix, and $\mathsf{done}$ halts.
