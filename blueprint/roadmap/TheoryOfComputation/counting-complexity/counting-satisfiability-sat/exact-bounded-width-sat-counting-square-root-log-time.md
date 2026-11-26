# Exact bounded-width SAT counting in square-root-logarithmic subexponential time

For each natural $k\ge2$ there are one deterministic primitive finite multitape machine, two designated output tapes (count and answer), positive reals $C,A,S$ and positive naturals $d,e$, chosen independently of the formula. For all $n\ge0$ and all CNFs on the variable set $[n]$ whose clauses have at most $k$ literals, the machine halts with the exact number of satisfying assignments and its positivity bit (also recorded as the terminal state). Clauses are finite sets of signed literals and formulas are finite sets of clauses. The count is over all $n$ variables, including unused ones; the count tape has canonical little-endian digits (one zero bit for count zero), representing the count and having length at most $n+1$. The answer tape is exactly the single bit on an otherwise blank tape, and the count tape is likewise in its initial-head layout for the count word.

The input begins with unary $n$ followed by a framed list of clauses. Literal codes are $2i+b$ with the sign bit $b$, in increasing order in each clause; clauses are sorted lexicographically by those lists. Codes are unary; at each list level a leading one introduces each framed element and a zero terminates the list, and framing replaces a bit $b$ by $1b$ and terminates with zero. Write $L$ for the length in bits of this code. With natural logarithms, the time is at most

$$
C(L+1)^d\,2^{A n(\log\log(n+16))^2/\sqrt{\log(n+16)}}.
$$

At each prefix (including before the first step and at halt), the sum of widths of the tape intervals from least to greatest visited cells is at most $S(L+1)^e$; the initial input interval is included. A nonhalting step scans a single designated tape for its control state and moves one cell or writes there as prescribed.

## Depends on

- Canonically encoded bounded-width CNFs, the primitive finite tape machine, and its interval monitor as specified above.

## Proof depends on

- Construction of the exact counting transducer, its bit-operation runtime estimate, and a prefix-by-prefix tape interval bound including output and input cells.

## Expansion

Prove that the canonical code round trips including empty clauses, unused variables and zero outputs. Bridge the primitive tape semantics and visited interval monitor to a native machine before comparing with other formulations of ETH. The displayed exponent is $o(n)$ but is not shown bounded by $n^{1-\eta}$ for any fixed $\eta>0$; this is not a refutation of the power-saving Weak ETH premise used for tape multiplication, and it does not assert the sharper manuscript time bounds.

## Related topics

- [ETH and SETH](../../fine-grained-complexity/fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md). The displayed bound is subexponential in the variable count in the specified model with a polynomial input-length factor. Comparison with other statements of ETH requires a model and encoding bridge.

## Sources

- OpenAI, [binary arithmetic, formula syntax, machine and `exact_count_and_sat`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SubexponentialSAT.lean#L3-L218).
