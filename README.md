# Spatial scale space from hemigroup axioms: affine covariance and shape adaptation — release v0.1

This repository is the verification artifact of the article of the same name (the PDF is at the
root). It is an export of the development repository at revision `cf033f6`, restricted to
what the article's statements rest on; the development repository also holds the material of
other modules of the same theory and stays private until they are released.

## What is here

- `Formalization/` — the Lean 4 development: the transitive import closure of every module that a
  numbered statement of the article names (160 modules), with the toolchain pinned
  in-tree (`lean-toolchain`, `lake-manifest.json`).
- `Formalization/CIAxiomGuard.lean` — prints the axiom usage of every named declaration.
- `blueprint/trust-boundary.txt`, `blueprint/AXIOMS.md` — the 12 interface names of
  the full development, each with the page-verified citation it rests on and the step it carries
  beyond its source; `blueprint/AXIOMS-verbatim.md`, where it is present, sets the sources' own
  wording beside each entry. Section I of the paper says which of them the article's theorems rest on.
- `blueprint/src/parts/` — the statements and proofs of record of the article's sections 2, 4, 5 (the
  blueprint's chapters of the same numbers), with the `\lean{}` tag naming the declaration
  behind each statement; a chapter of another module is included where the article transcribes a
  statement from it.
- `paper/` — the article's sources.
- `notes/` — the process account, the external reviews verbatim, and the response plan.
- `records/affine/fig-rank-deficient-step.py`, `records/affine/fig-rank-deficient-step-output.txt`, `records/affine/fig-shape-plane.py`, `records/affine/fig-shape-plane-output.txt`, `records/affine/fig-cones-plane.py`, `records/affine/fig-cones-plane-output.txt`, `records/affine/check-grid-matern-cross-shape.py`, `records/affine/check-grid-matern-cross-shape-output.txt`, `records/affine/check-gaussian-matern-step.py`, `records/affine/check-gaussian-matern-step-output.txt`, `records/affine/ai-figures-2026-10-11`, `records/affine/ai-figures-2026-10-13.md`, `records/affine/ai-figures-2026-11-04`, `records/affine/INDEX-complete-proofs.md`, `records/affine/gen-complete-proofs-index.py` — the files that the article names by these paths.

## Verifying

    cd Formalization
    lake exe cache get        # Mathlib's prebuilt oleans
    lake build
    lake env lean CIAxiomGuard.lean

The last command prints, for `AffineHemigroup.affine_rigidity`, the axioms it rests on: Lean's three
logical axioms and the interface names section I of the paper lists.

## Statements and declarations

| blueprint node (chapter) | declarations |
|---|---|
| `thm:cited-A1 (02)` | `AffineHemigroup.density_of_integrable_charFun` |
| `thm:cited-A2 (02)` | `AffineHemigroup.sato_polar_criterion` |
| `thm:cited-A3 (02)` | `AffineHemigroup.levy_khintchine_exists`, `AffineHemigroup.levy_khintchine_unique`, `AffineHemigroup.levy_khintchine_converse` |
| `thm:cited-A4 (02)` | `AffineHemigroup.selfDecomposable_infinitelyDivisible` |
| `thm:cited-A5 (02)` | `AffineHemigroup.operatorSelfDecomposable_infinitelyDivisible` |
| `thm:cited-A6 (02)` | `AffineHemigroup.khintchine_null_array` |
| `thm:cited-A8 (02)` | `AffineHemigroup.wolfe_symmetric_unimodal` |
| `thm:cited-A9 (02)` | `AffineHemigroup.gelfand_naimark_logMajorized` |
| `thm:cited-A10 (02)` | `AffineHemigroup.schoenberg_radial_bernstein` |
| `thm:cited-A11 (02)` | `AffineHemigroup.karamata_tauberian_zero` |
| `prop:line-levy-unique (02)` | `AffineHemigroup.line_levy_unique` |
| `def:gw-cascade-family (04)` | `AffineHemigroup.IsWedgeDatum`, `AffineHemigroup.wedgePairs`, `AffineHemigroup.IsGWOperatorFamily`, `AffineHemigroup.IsSingleOperator`, `AffineHemigroup.IsGWCascadeFamily`, `AffineHemigroup.loewnerLE`, `AffineHemigroup.rayLE`, `AffineHemigroup.push`, `AffineHemigroup.act`, `AffineHemigroup.glSet`, `AffineHemigroup.simSet`, `AffineHemigroup.wedge_zero_le`, `AffineHemigroup.wedge_zero_one_mem`, `AffineHemigroup.isWedgeDatum_loewner`, `AffineHemigroup.isWedgeDatum_ray`, `AffineHemigroup.glSet_isClosedSubgroupGL`, `AffineHemigroup.charFun_push`, `AffineHemigroup.simSet_isClosedSubgroupGL` |
| `def:affine-cascade-family (04)` | `AffineHemigroup.IsAffineCascadeFamily`, `AffineHemigroup.affineGaussian`, `AffineHemigroup.charFun_affineGaussian`, `AffineHemigroup.affineGaussian_carried_by_range` |
| `lem:operators-to-kernels (04)` | `AffineHemigroup.operators_to_kernels_repr`, `AffineHemigroup.operators_to_kernels_unique`, `AffineHemigroup.operators_to_kernels_converse`, `AffineHemigroup.operators_to_kernels_transport`, `AffineHemigroup.operators_to_kernels_transport_iff`, `AffineHemigroup.operators_to_kernels_continuity`, `AffineHemigroup.operators_to_kernels_gw`, `AffineHemigroup.operators_to_kernels_affine`, `AffineHemigroup.operators_to_kernels_isotropic`, `AffineHemigroup.gaussDensity`, `AffineHemigroup.gaussL1` |
| `lem:operators-to-kernels-families (04)` | `AffineHemigroup.IsIsotropicOperatorFamily`, `AffineHemigroup.IsConvOnPairs` |
| `lem:kernels-to-operators (04)` | `AffineHemigroup.kernels_to_operators_continuity`, `AffineHemigroup.kernels_to_operators_gw`, `AffineHemigroup.kernels_operators_correspondence`, `AffineHemigroup.kernels_to_operators_isotropic` |
| `prop:isotropic-corner (04)` | `AffineHemigroup.isotropic_corner_slice`, `AffineHemigroup.isotropic_corner_gauge`, `AffineHemigroup.isotropic_corner_gauge_forall`, `AffineHemigroup.isotropic_corner_gauge_unique`, `AffineHemigroup.isotropic_corner_rescale`, `AffineHemigroup.isotropic_corner_gl_determined`, `AffineHemigroup.isotropic_corner_sim_not_determined` |
| `lem:affine-gauge (04)` | `AffineHemigroup.affine_gauge`, `AffineHemigroup.affine_gauge_slice` |
| `lem:parameter-space (04)` | `AffineHemigroup.stab_isClosedSubgroupGL`, `AffineHemigroup.stab_isCompact_of_isFull`, `AffineHemigroup.carried_by_subspace_of_not_isCompact`, `AffineHemigroup.stab_dirac_ebasis`, `AffineHemigroup.isFull_of_isRotationInvariant`, `AffineHemigroup.parameter_space_tfae`, `AffineHemigroup.parameter_space_index_bijOn`, `AffineHemigroup.parameter_space_index_unique`, `AffineHemigroup.parameter_space_atoms`, `AffineHemigroup.parameter_space_scheme`, `AffineHemigroup.gram_glSet_eq_pdSet`, `AffineHemigroup.parameter_space_diag_example` |
| `thm:cascade-infinitely-divisible (04)` | `AffineHemigroup.cascade_interval_infinitelyDivisible`, `AffineHemigroup.chain_infinitelyDivisible`, `AffineHemigroup.gw_family_infinitelyDivisible`, `AffineHemigroup.isotropic_family_infinitelyDivisible`, `AffineHemigroup.chain_loewner`, `AffineHemigroup.chain_ray_zero`, `AffineHemigroup.chain_ray`, `AffineHemigroup.chain_stepSet`, `AffineHemigroup.stepSet_loewner`, `AffineHemigroup.stepSet_ray`, `AffineHemigroup.stepSet_stable` |
| `lem:charfn-one-on-subspace (04)` | `AffineHemigroup.charFun_one_on_subspace`, `AffineHemigroup.eq_dirac_of_charFun_one_near_zero` |
| `lem:affine-reduction (04)` | `AffineHemigroup.affine_reduction` |
| `lem:single-ratio-cauchy (04)` | `AffineHemigroup.single_ratio_cauchy` |
| `thm:rank-deficient-step (04)` | `AffineHemigroup.rank_deficient_step`, `AffineHemigroup.rank_deficient_step_converse` |
| `thm:affine-rigidity (04)` | `AffineHemigroup.affine_rigidity`, `AffineHemigroup.affine_rigidity_kernel` |
| `prop:affine-rigidity-boundary (04)` | `AffineHemigroup.affine_rigidity_interior`, `AffineHemigroup.affine_rigidity_boundary_family`, `AffineHemigroup.IsAffineCascadeFamilyNoK2`, `AffineHemigroup.boundaryFamily` |
| `thm:affine-rigidity-operators (04)` | `AffineHemigroup.affine_rigidity_operators` |
| `prop:glplus-families (05)` | `AffineHemigroup.glPlusSet_isClosedSubgroupGL`, `AffineHemigroup.exists_joint_reflection`, `AffineHemigroup.invariant_gl_of_invariant_glPlus`, `AffineHemigroup.isWedgeDatum_glPlus_iff`, `AffineHemigroup.gw_family_glPlus_iff`, `AffineHemigroup.glPlus_loewner_rigidity`, `AffineHemigroup.glPlus_line_counterexample`, `AffineHemigroup.gw_operator_family_glPlus_iff` |
| `lem:loewner-scale-shape (05)` | `AffineHemigroup.scale_shape_coords`, `AffineHemigroup.loewner_iff_scale_shape`, `AffineHemigroup.loewner_no_order_within_scale`, `AffineHemigroup.loewner_speed_limit`, `AffineHemigroup.loewner_speed_limit_converse`, `AffineHemigroup.loewner_plane_disc` |
| `prop:invariant-orders (05)` | `AffineHemigroup.stepLE_iff_factor`, `AffineHemigroup.stepLE_invariant`, `AffineHemigroup.invariant_relation_eq_stepLE`, `AffineHemigroup.stepLE_order_props`, `AffineHemigroup.stepLE_compose`, `AffineHemigroup.stepLE_chain_of_mem`, `AffineHemigroup.stepLE_trans_tfae`, `AffineHemigroup.step_composite_example`, `AffineHemigroup.infCone_props` |
| `lem:spectral-cones (05)` | `AffineHemigroup.eigUp_spec`, `AffineHemigroup.partialSum_eigUp_isLeast`, `AffineHemigroup.partialSum_eigUp_lipschitz`, `AffineHemigroup.eigUp_add_majorized`, `AffineHemigroup.logSpec_product_majorized`, `AffineHemigroup.symCone_mem_iff`, `AffineHemigroup.symCone_majorization`, `AffineHemigroup.specCone_isClosedConvexCone`, `AffineHemigroup.orthInvariant_cone_eq_specCone`, `AffineHemigroup.orthInvariant_pointed_cone_sign`, `AffineHemigroup.expSet_specCone` |
| `def:cone-orders-curves (05)` | `AffineHemigroup.mderiv`, `AffineHemigroup.IsCausalCurve`, `AffineHemigroup.causalLE`, `AffineHemigroup.causalPlusLE` |
| `thm:cone-orders (05)` | `AffineHemigroup.coneField_eq`, `AffineHemigroup.causalLE_iff_expSet`, `AffineHemigroup.causalLE_order`, `AffineHemigroup.closed_order_tangent_wedge`, `AffineHemigroup.closed_order_cone_tfae`, `AffineHemigroup.closed_order_without_cone`, `AffineHemigroup.causalPlus_wedge`, `AffineHemigroup.causalPlus_ray` |
| `prop:stable-order-generated (05)` | `AffineHemigroup.stableGenCone_props`, `AffineHemigroup.psdSet_cone_props`, `AffineHemigroup.stable_order_zero`, `AffineHemigroup.stable_order_pos`, `AffineHemigroup.stable_order_infty`, `AffineHemigroup.stableExpCone_tangent`, `AffineHemigroup.stable_order_loewner_coords` |
| `prop:affine-orbits (05)` | `AffineHemigroup.affine_orbit_covariance`, `AffineHemigroup.affine_orbit_ray_cascade`, `AffineHemigroup.affine_orbit_no_cross_shape`, `AffineHemigroup.matern_orbit`, `AffineHemigroup.maternRay_W_nonneg` |
| `prop:ray-families (05)` | `AffineHemigroup.ray_families`, `AffineHemigroup.ray_families_converse` |
| `lem:elliptical-stable (05)` | `AffineHemigroup.stableConst_pos_finite`, `AffineHemigroup.stableExp_eq_lintegral`, `AffineHemigroup.stableDensity_act`, `AffineHemigroup.ellipticalStable_exists_unique`, `AffineHemigroup.ellipticalStable_props`, `AffineHemigroup.ellipticalStable_orbit` |
| `lem:stable-tail (05)` | `AffineHemigroup.stable_tail` |
| `prop:stable-step-cone (05)` | `AffineHemigroup.stable_step_cone_tfae`, `AffineHemigroup.stable_step_cone_increment`, `AffineHemigroup.stable_step_increments`, `AffineHemigroup.stable_density_order_iff`, `AffineHemigroup.stableLE_partialOrder`, `AffineHemigroup.stableLE_rays_not_rank_deficient`, `AffineHemigroup.stableLE_scale_shape`, `AffineHemigroup.stableLE_scale_shape_converse`, `AffineHemigroup.stableLE_any_eigenframe` |
| `prop:stable-exponent-cone (05)` | `AffineHemigroup.stable_exponent_cone`, `AffineHemigroup.stableExpCone_props` |
| `prop:orbit-step-cone (05)` | `AffineHemigroup.dilRatio_mem`, `AffineHemigroup.profileLaw_exists_unique`, `AffineHemigroup.profileLaw_props`, `AffineHemigroup.orbit_density_order_iff`, `AffineHemigroup.orbit_density_order_increment`, `AffineHemigroup.orbit_density_order_props`, `AffineHemigroup.orbit_density_order_stable`, `AffineHemigroup.orbit_density_order_bounded` |
| `lem:dilation-ratio (05)` | `AffineHemigroup.dilRatio_monotone`, `AffineHemigroup.dilRatio_lt_sq`, `AffineHemigroup.dilRatio_exponents`, `AffineHemigroup.dilRatio_rung`, `AffineHemigroup.dilRatio_exponents_stable`, `AffineHemigroup.dilRatio_exponents_bounded`, `AffineHemigroup.dilRatio_dyadic` |
| `prop:tempered-step-cone (05)` | `AffineHemigroup.tempered_profile_exists`, `AffineHemigroup.tempered_step_cone`, `AffineHemigroup.tempered_exp_example`, `AffineHemigroup.tempered_subordinated_example`, `AffineHemigroup.matern_endpoint`, `AffineHemigroup.tempered_exponential_moments` |
| `prop:log-orbit-rays (05)` | `AffineHemigroup.log_orbit_rays`, `AffineHemigroup.matern_log_orbit_rays` |
| `prop:matern-steps (05)` | `AffineHemigroup.matern_steps` |
| `prop:rational-symbols (05)` | `AffineHemigroup.rational_symbols`, `AffineHemigroup.rational_symbols_examples` |
| `prop:bounded-profile-rays (05)` | `AffineHemigroup.bounded_profile_rays` |
| `prop:matern-cross-shape (05)` | `AffineHemigroup.matern_cross_shape` |
| `lem:matern-kernel-hessian (05)` | `AffineHemigroup.matern_kernel`, `AffineHemigroup.matern_kernel_hessian` |
| `prop:matern-negative-mass (05)` | `AffineHemigroup.maternIncrement_eq_integral`, `AffineHemigroup.matern_negative_mass_off_origin`, `AffineHemigroup.matern_negative_mass_near_origin`, `AffineHemigroup.matern_negative_mass_log`, `AffineHemigroup.matern_negative_mass_plane`, `AffineHemigroup.matern_negative_mass_plane_example` |
| `lem:gw-kernels-from-origin (05)` | `AffineHemigroup.gw_family_restrict`, `AffineHemigroup.gw_kernels_from_origin`, `AffineHemigroup.gw_kernels_from_origin_unique`, `AffineHemigroup.gw_kernels_from_origin_converse` |
| `prop:frame-families (05)` | `AffineHemigroup.frame_family_cascade`, `AffineHemigroup.frame_family_gaussian`, `AffineHemigroup.frame_family_only_gaussian` |
| `prop:fixed-frame-families (05)` | `AffineHemigroup.fixed_frame_families`, `AffineHemigroup.fixed_frame_families_converse` |
| `prop:gw-ray-families (05)` | `AffineHemigroup.selfDecomposable_charFun_ne_zero`, `AffineHemigroup.gw_ray_families`, `AffineHemigroup.gw_ray_families_unique`, `AffineHemigroup.gw_ray_families_gl`, `AffineHemigroup.gw_ray_families_gl_converse` |
| `lem:gw-kernels-self-decomposable (05)` | `AffineHemigroup.gw_kernels_selfDecomposable`, `AffineHemigroup.gw_kernels_hasNoZeros`, `AffineHemigroup.gw_family_determined_by_kernels` |
| `prop:similarity-ray-families (05)` | `AffineHemigroup.similarity_ray_parameter`, `AffineHemigroup.similarity_ray_families`, `AffineHemigroup.similarity_ray_kernels`, `AffineHemigroup.similarity_ray_isotropic`, `AffineHemigroup.similarity_ray_two_families`, `AffineHemigroup.similarity_row_isotropic_members` |
| `prop:diagonal-ray-families (05)` | `AffineHemigroup.diagonal_ray_parameter`, `AffineHemigroup.diagonal_ray_families`, `AffineHemigroup.diagonal_ray_frame`, `AffineHemigroup.diagonal_loewner_products`, `AffineHemigroup.diagonal_rays_no_product`, `AffineHemigroup.diagonal_rays_off_frame` |
| `prop:anisotropy-budget (05)` | `AffineHemigroup.anisotropy_budget`, `AffineHemigroup.anisotropy_budget_converse` |
| `prop:one-parameter-families (05)` | `AffineHemigroup.one_parameter_families`, `AffineHemigroup.one_parameter_families_converse`, `AffineHemigroup.isExpContracting_iff`, `AffineHemigroup.one_parameter_origin`, `AffineHemigroup.one_parameter_curve`, `AffineHemigroup.one_parameter_gaussian`, `AffineHemigroup.one_parameter_products`, `AffineHemigroup.one_parameter_stable_member` |
| `prop:similarity-stable-family (05)` | `AffineHemigroup.sim_stable_parts_ordered`, `AffineHemigroup.sim_stable_bounded_shape`, `AffineHemigroup.sim_stable_not_shape_blind` |
| `prop:similarity-orbit-family (05)` | `AffineHemigroup.sim_orbit_id_increment`, `AffineHemigroup.sim_orbit_bounded_shape`, `AffineHemigroup.sim_orbit_index_zero`, `AffineHemigroup.sim_orbit_log` |
| `prop:similarity-general-sandwich (05)` | `AffineHemigroup.sim_general_covariance`, `AffineHemigroup.sim_general_id_increment`, `AffineHemigroup.sim_general_finite_increment`, `AffineHemigroup.sim_general_rank_one_limit`, `AffineHemigroup.sim_general_rank_one_exp_limit`, `AffineHemigroup.sim_general_sandwich` |
| `prop:similarity-general-bounded-shape (05)` | `AffineHemigroup.anisotropy_functionals`, `AffineHemigroup.sim_bounded_shape_levy`, `AffineHemigroup.sim_bounded_shape_exp`, `AffineHemigroup.sim_bounded_shape_moments` |
| `prop:similarity-degenerate-family (05)` | `AffineHemigroup.degenerate_cascade`, `AffineHemigroup.degenerate_unbounded`, `AffineHemigroup.degenerate_rotation_invariant_limit` |
| `prop:similarity-line-family (05)` | `AffineHemigroup.line_family_levy`, `AffineHemigroup.line_family_cascade`, `AffineHemigroup.line_family_functionals`, `AffineHemigroup.line_family_levy_not_shape_blind`, `AffineHemigroup.line_family_not_shape_blind` |
| `prop:similarity-general-index-zero (05)` | `AffineHemigroup.sim_index_zero_levy`, `AffineHemigroup.sim_index_zero_exp`, `AffineHemigroup.sim_index_zero_blowup` |
| `prop:similarity-cascade-families (05)` | `AffineHemigroup.sim_cascade_infinitelyDivisible`, `AffineHemigroup.sim_cascade_general`, `AffineHemigroup.sim_cascade_elliptical` |
| `prop:similarity-stable-order-families (05)` | `AffineHemigroup.stablePlusLE_order`, `AffineHemigroup.stable_order_gl_row`, `AffineHemigroup.stable_order_gl_row_examples` |
| `prop:similarity-stable-order-kernels (05)` | `AffineHemigroup.stable_order_sim_kernels`, `AffineHemigroup.stable_order_sim_isotropic`, `AffineHemigroup.stable_order_sandwich`, `AffineHemigroup.loewner_order_sandwich`, `AffineHemigroup.stable_order_cell_strict` |
| `prop:diagonal-stable-order-families (05)` | `AffineHemigroup.diagonal_stable_datum`, `AffineHemigroup.diagonal_stable_frame`, `AffineHemigroup.diagonal_stable_sources`, `AffineHemigroup.diagonal_stable_gaussian_excluded`, `AffineHemigroup.diagonal_stable_not_product`, `AffineHemigroup.diagonal_stable_mixed` |
| `thm:wedge-axis (05)` | `AffineHemigroup.wedge_axis_chain`, `AffineHemigroup.wedge_axis_not_psd`, `AffineHemigroup.wedge_axis_singular`, `AffineHemigroup.wedge_axis_index`, `AffineHemigroup.wedge_axis_stable`, `AffineHemigroup.wedge_axis_non_gaussian`, `AffineHemigroup.wedge_axis_row`, `AffineHemigroup.wedge_axis_row_members` |
| `prop:wedge-axis-profiles (05)` | `AffineHemigroup.wedge_axis_profiles`, `AffineHemigroup.wedge_axis_profiles_stable`, `AffineHemigroup.rowLaws_coe_eq_coneLaws`, `AffineHemigroup.wedge_axis_cell`, `AffineHemigroup.wedge_axis_cell_gaussian`, `AffineHemigroup.wedge_axis_cone_laws`, `AffineHemigroup.wedge_axis_cone_laws_gaussian` |
| `prop:shape-adapted-apertures (05)` | `AffineHemigroup.shape_adapted_step`, `AffineHemigroup.shape_adapted_gaussian`, `AffineHemigroup.shape_adapted_scheme` |
| `def:isotropic-origin-datum (03)` | `AffineHemigroup.OriginDatum`, `AffineHemigroup.OriginDatum.levyMeasure`, `AffineHemigroup.OriginDatum.exponentL`, `AffineHemigroup.OriginDatum.exponent`, `AffineHemigroup.OriginDatum.profileAtOrigin`, `AffineHemigroup.OriginDatum.IsSubordinated`, `AffineHemigroup.IsLawOf`, `AffineHemigroup.sphereArea`, `AffineHemigroup.polarProfileOf`, `AffineHemigroup.sphereArea_eq_toSphere`, `AffineHemigroup.OriginDatum.tendsto_profileAtOrigin`, `AffineHemigroup.OriginDatum.polar_decomposition` |
| `lem:isotropic-exponent-log (03)` | `AffineHemigroup.isotropic_exponent_log_bound`, `AffineHemigroup.isotropic_exponent_log_limit`, `AffineHemigroup.OriginDatum.tailConst` |
| `def:isotropic-kernel-family (03)` | `AffineHemigroup.IsIsotropicCascadeFamily`, `AffineHemigroup.IsIncreasingBijection`, `AffineHemigroup.IsGauge`, `AffineHemigroup.isGauge_iff_isIncreasingBijection` |
| `lem:radial-marginal (03)` | `AffineHemigroup.radial_marginal`, `AffineHemigroup.radial_marginal_eq_dirac`, `AffineHemigroup.radial_marginal_ops`, `AffineHemigroup.marginal` |
| `lem:isotropic-marginal-family (03)` | `AffineHemigroup.isotropic_marginal_family`, `AffineHemigroup.isotropic_marginal_cascadeData` |
| `thm:isotropic-classification (03)` | `AffineHemigroup.isotropic_classification`, `AffineHemigroup.isotropic_classification_origin`, `AffineHemigroup.isotropic_classification_unique` |

## Licence

Lean sources under Apache 2.0, text under CC BY 4.0 (`LICENSES/`).
