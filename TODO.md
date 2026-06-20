# TODO

## Mathlib candidate audit

- Check whether the lemmas in `LinearAlgebraLemma/ForMathlib/Basis.lean` already exist under nearby names such as `Basis.map_trans`, `Basis.map_reindex`, or `Basis.reindex_map`.
- Check whether `toMatrix_basis_map`, `matrix_conj`, and `matrix_basis_reindex` are subsumed by existing `LinearMap.toMatrix` reindexing API.
- Prioritize upstreaming `charpoly_dualmap_eq_charpoly`; it is the cleanest standalone candidate.
- Consider upstreaming `lie_dual` as an anti-hom compatibility lemma for `LinearMap.dualMap`.
- Consider upstreaming `exists_maximal_smul_le_of_ne_bot_of_fg` as a Nakayama corollary after finding the best Mathlib name and location.

## Local cleanup

- Rename remaining `aux_*` lemmas in the project files when their role becomes stable.
- Decide whether `upperLeftProj` and `upperLeftIncl` should stay as project vocabulary or be generalized into a polished product-block API.
- Revisit the reduction-mod-maximal-ideal section in `CyclicOfCoprime.lean`; several local lemmas there may become smaller after upstream base-change API improves.

