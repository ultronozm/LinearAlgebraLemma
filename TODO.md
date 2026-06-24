# TODO

## Mathlib candidate audit

- Audit result: current Mathlib does not appear to have the staged basis transport lemmas now named `Module.Basis.map_trans`, `Module.Basis.map_symm`, `Module.Basis.map_symm_self`, and `Module.Basis.reindex_map`.
- Audit result: current Mathlib already has `LinearEquiv.conj_symm_conj`, `LinearEquiv.conj_conj_symm`, and `Matrix.charpoly_toLin'`; the local duplicate candidates were removed.
- Audit result: `LinearMap.toMatrix_map_equiv` is a convenience wrapper around existing `LinearMap.toMatrix_map_left` and `LinearMap.toMatrix_map_right`; `LinearMap.toMatrix_reindex` still appears to fill a small gap.
- Prioritize upstreaming `LinearMap.charpoly_dualMap`; it is the cleanest standalone candidate.
- Consider upstreaming `LinearMap.dualMap_lie` as an anti-hom compatibility lemma for `LinearMap.dualMap`.
- Consider upstreaming `exists_maximal_smul_le_of_ne_bot_of_fg` as a Nakayama corollary after finding the best Mathlib name and location.

## Local cleanup

- Rename remaining `aux_*` lemmas in the project files when their role becomes stable.
- Decide whether `upperLeftProj` and `upperLeftIncl` should stay as project vocabulary or be generalized into a polished product-block API.
- Revisit the reduction-mod-maximal-ideal section in `CyclicOfCoprime.lean`; several local lemmas there may become smaller after upstream base-change API improves.
