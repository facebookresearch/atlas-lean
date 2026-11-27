# Thomason model structures for positive strict finite dimensions and dimension omega

On simplicial sets take the Kan–Quillen model structure, with weak equivalences the maps whose realizations induce bijections on components and all positive based homotopy groups, fibrations by right lifting against horns, and cofibrations the monomorphisms. In dimension $\omega$ and separately for every finite $n\ge1$, take small strict globular categories of that dimension. The adjunction is $L=c\,\mathrm{Sd}^2\dashv R=\mathrm{Ex}^2N_{\rm St}$, using the Street nerve of the orientals and its left adjoint, with their finite-dimensional versions in dimension $n$.

There is a model structure with weak equivalences and fibrations pulled back along $R$ from simplicial sets, and cofibrations given by left lifting against their intersection. The images under $L$ of the simplex-boundary inclusions detect trivial fibrations by right lifting; images of the horns detect fibrations. Both resulting weak factorization systems exist. The category is complete, cocomplete and locally presentable. The model structure is left and right proper (pushout along cofibrations and pullback along fibrations preserve weak equivalences). The left adjoint preserves cofibrations and trivial cofibrations; for each simplicial set $K$ and each fibrant $Y$, a map $LK\to Y$ is a weak equivalence exactly when the adjoint $K\to RY$ is one.

## Depends on

- Kan–Quillen model structure, strict globular categories in the two ranges, orientals, subdivision and extension adjunctions.

## Proof depends on

- Transfer of the two weak factorization systems, preservation under the necessary pushouts and pullbacks, local presentability and the unit/counit weak-equivalence criterion.

## Expansion

Establish the simplicial base model separately. Verify the Street adjunction and finite truncation comparison before transfer. Then check the generating boundary/horn image tests, properness and Quillen-equivalence criterion for the exact right adjoint.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThomasonModelStructures.lean#L2460-L2462) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThomasonModelStructures.lean).
