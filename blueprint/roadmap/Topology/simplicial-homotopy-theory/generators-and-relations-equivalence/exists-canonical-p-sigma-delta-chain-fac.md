# Exists canonical P sigma delta Chain factorization

Every morphism between canonical presented simplex objects factors as a pure degeneracy
followed by an admissible face-chain. Uses `exists_P_σ_P_δ_factorization` for the
`P_σ / P_δ` split, reduces the intermediate object with dependent object induction
`SimplexCategoryGenRel.rec`, and finishes with `DeltaChain.exists_admissible_chain_of_P_delta`.
