# Preplaced queens

The queen $(\alpha, \beta)$ (column $\alpha$, row $\beta$) is preplaced when entry $\alpha$ of row $\beta$ of the stored board is true; a missing row or a missing entry of a row reads as false. The test reads the stored rows as they are, whatever their lengths: on the one-row input $[[\mathrm{false}, \mathrm{true}]]$, entry $1$ of row $0$ is true although it lies outside the nominal $1 \times 1$ board. That the board is square is a separate condition, part of well-formedness.
