# Changelog

All releases of this module are recorded here, newest first, with what changed and why, and in
particular which statements were renumbered, strengthened, weakened or withdrawn (hub `RELEASES.md`,
rule 2).

## v0.1 — 2026-11-04 — first release of the affine paper: affine covariance and shape adaptation

The article *Spatial scale space from hemigroup axioms: affine covariance and shape adaptation*. It asks which
scale-space families exist in dimension $d \ge 2$ when the kernel and the cascade are free, under the hemigroup axioms, for a group $G$ of
linear maps and an order $W$ on scale matrices. It describes the families of the general linear group, the similarities and the positive diagonal
group along the ray, stable and Loewner orders, completely in some cases and by bounds or examples in others. Theorems 3.6 and 4.21 and
Proposition 4.22 give the general linear group along the chain of cones.

It follows the isotropic paper (`iso-v0.1`), the line paper and the cone paper, and restates in its section 2 what it uses from them, by their released
statement numbers. It went through three external reviews by AI systems, saved under `notes/` with the plan that records what was done with each finding.

Every statement it numbers is machine-checked in Lean 4, on Lean's three logical axioms and five cited facts, C1 to C5, which are ledger entries A6, A3, A5, A9
and A2. Twenty statements are printed with a sketch; `records/affine/INDEX-complete-proofs.md` says where the complete proof of each is. The first release, so nothing is renumbered, weakened or withdrawn.
