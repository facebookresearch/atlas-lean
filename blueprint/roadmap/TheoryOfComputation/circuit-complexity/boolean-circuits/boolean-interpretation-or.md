# Boolean OR as a left fold

For every natural number $a$ and truth values
$x_0, \dots, x_a$, the Boolean interpretation of the OR gate with $a + 1$ inputs, applied to
$x_0, \dots, x_a$, returns $(\cdots((\mathrm{false} \lor x_0) \lor x_1) \cdots) \lor x_a$,
folding disjunction over the inputs from left to right starting from false.
