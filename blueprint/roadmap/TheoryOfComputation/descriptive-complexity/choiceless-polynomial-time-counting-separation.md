# A polynomial-time linear-system query outside choiceless polynomial time with counting

Take any finite set with eight binary relations $\mathrm{Ed},\mathrm{Cf},\mathrm{EB},\mathrm{VB},I$ and $Z_\delta$ for $\delta\in\mathbb F_3$. Let $E$ and $C$ be the diagonal true sets of Ed and Cf respectively. Define $c_{ya}=\sum_{x\in E:I(a,x)}\sum_{\delta:Z_\delta(y,x)}\delta$. The query asks for $\lambda:C\to\mathbb F_3$, $\mu:E\to\mathbb F_3$ such that, for each $t\in C$, $\sum_{a\in C:\mathrm{VB}(t,a)}\lambda_a=1$, and for $(t,y)$ with some $a,x$ satisfying $\mathrm{VB}(t,a),I(a,x),\mathrm{EB}(y,x)$,

$$\mu_y=\sum_{a\in C:\mathrm{VB}(t,a)}\lambda_a c_{ya}.$$

Here $a\in C$ and $x\in E$; no partition or input promise is required, and several $Z_\delta$ terms may contribute to one pair. The query is invariant under every bijection preserving the eight relations: it restricts to bijections of $E$ and $C$, under which the sums and incident witnesses reindex and the functions $\lambda$ and $\mu$ transport in both directions.

There is a Boolean answer function on ordered inputs and one deterministic finite-stack machine in the Mathlib `TM2ComputableInPolyTime` model computing that function, with a finite alphabet for each stack. From an enumeration of $N$ elements its input is $N$ copies of the optional-symbol letter `none`, then a `some 0` separator, then the eight binary relation tables in order Ed, Cf, EB, VB, I, $Z_0,Z_1,Z_2$, with pairs in lexicographic index order. Each table bit is encoded as `some 0` or `some 1`. The Boolean output is the corresponding one-letter list. Its answer is true precisely when the system is solvable, for every enumeration.

No program of the source's choiceless language, with polynomial bounds in the number of atoms, has bounded acceptance precisely on those inputs. It operates on hereditarily finite sets over atoms, with pairs, union, unique-element extraction, cardinality, relation tests, comprehensions, a finite dynamic function signature, and parallel updates. Bounded acceptance means that some run stage within the time bound is both halted and accepting, and that the count of hereditarily occurring objects through that stage (including term and rule intermediates) is within the other bound. For a false input there is no such bounded accepting stage; the definition does not require a rejecting halt.

## Depends on

- The ternary edge-weight system above, the encoded finite-stack `TM2` contract, and the operational hereditarily finite set syntax and full occurrence bound.

## Proof depends on

- An actual polynomial-time Gaussian elimination machine correct on every enumeration, and model-specific nondefinability via the symmetry bound.

## Expansion

Prove the table encoding and the ordered algorithm correct on all finite inputs, including malformed incidence data. Establish the model correspondence for the exact resource account before importing the symmetry lower bound; do not infer a separation for a different CPT formalism.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ChoicelessPolynomialTime.lean#L549-L555) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ChoicelessPolynomialTime.lean).
