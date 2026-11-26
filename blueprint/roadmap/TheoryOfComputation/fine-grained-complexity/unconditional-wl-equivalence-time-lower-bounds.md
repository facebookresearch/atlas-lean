# Unconditional fixed-dimension WL equivalence time lower bounds

There are an absolute real $c>0$ and $k_0$ such that for every fixed integer $k\ge k_0$, for each of joint and separate $k$-tuple refinement and for each input class below, any deciding machine of one of the two specified models has worst-case time at least $n^{ck}$ for all sufficiently large orders $n$ (the threshold is chosen after the convention, class and machine). Inputs are pairs of equal-order simple uncolored graphs, either unrestricted, or both nonempty and with all vertex pairs joined by paths of length at most two. Encode one natural order (length-many ones then zero then its low-to-high base-two digits), then both full row-major adjacency matrices. Tuple colors start with equality and adjacency tables. Updates retain the old color and adjoin the multiset over replacement vertices of full vectors of old colors for replacing each coordinate (joint), or the separate multisets per coordinate (separate). Equivalence compares histograms of all tuples at every round. A decider halts on every encoded pair in its class and accepts exactly the equivalent pairs. The worst case is the maximum time over all order-$n$ pairs, assigning zero to pairs outside the class.

In the multitape model one step reads all scanned finite-alphabet symbols, changes state, overwrites each scanned cell and independently moves each head left/stay/right. The finite state and tape alphabet sizes are at least three, with state 0 starting, 1 accepting and 2 rejecting, and symbols 0 blank, 1 false and 2 true. Heads initially sit at origin, with the input on tape zero starting there and all other cells blank. Halting is absorbing; time is the least transition count to a halted state.

The RAM uses fixed finite registers and program locations. At order $n$ its width $w(n)$ is positive and bounded by a machine-dependent constant times $\lfloor\log_2(n+2)\rfloor+1$. Its machine data requires that **every** order-$n$ graph-pair encoding fit in $w(n)2^{w(n)}$ bits, in both input classes. Words and addresses range from $0$ to $2^{w(n)}-1$. Initially the program counter and registers are zero and memory word $a$ contains the $w(n)$ consecutive input bits starting at position $w(n)a$, low bit first and padded with zeros. No truncated packing of longer input is allowed. At a location the fixed finite instruction tree performs register computations, loads, stores and zero tests until a terminal jump or halt. It has no unbounded loop inside one tree. Register computations act on the **whole** fixed-length register tuple: for any natural width $w$, a fixed local multitape implementation must halt with the packed output register tuple in the prefix of tape zero upon input of the framed width followed by all input register words in register order, with exactly $w$ low-to-high bits per word. Its least halt time is bounded on every such tuple by $A(w+1)^b$ for natural constants fixed with the operation. As in the source `TM.outputs` check, this implementation requires a halted output prefix, not the TM2 reset convention or an accepting state. The RAM itself charges one step for the entire instruction tree; only the auxiliary local implementation charges each tape transition. RAM time is the least step count to a present Boolean answer, which is absorbing.

## Depends on

- Exact pair encoding, tuple refinement, diameter restriction and machine-specific time and worst case.

## Proof depends on

- Unconditional lower-bound reduction in each convention and input class, and machine simulation/overhead preserving a universal exponent.

## Expansion

Separate bit-machine and sequential word-RAM simulation, and validate the fixed word-operation bound before transferring a lower bound. Keep $n_0$ after the algorithm, input-class and convention quantifiers and $c$ before them. This exact model is not an oracle-RAM or a complexity separation assumption.

## Sources

- [Comparator statement: `OAI.WLTime.unconditional_time_lower_bound`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WeisfeilerLeman.lean#L267-L269)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/133.md)
- [Refinement and width-independent full graph encoding](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WeisfeilerLeman.lean#L9-L58)
- [Local multitape decider and operation-output conventions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WeisfeilerLeman.lean#L63-L129)
- [Word tuple ABI, machine input-capacity condition and one-tree step semantics](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WeisfeilerLeman.lean#L132-L219)
- [Unrestricted and two-diameter inputs and worst-time quantifier](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WeisfeilerLeman.lean#L221-L265)
