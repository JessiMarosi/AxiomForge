# Axiom Forge — RH Testing Compilation Summary

**Generated:** 2025-12-28  
**Policy:** deterministic, auditable, no speculation

---

## Counts
- **TESTED:** 3
- **FAILED:** 3
- **PASSED:** 0

---

## Entries

### 1) mertens_equivalence
- **Claim:** RH ⇔ Mertens / Möbius bound  
  *(M(x) = O(x^{1/2+η}) for all η > 0)*
- **Status:** FAILED
- **Failure Type:** Analytic infrastructure boundary
- **Failure Point:** `MiniProver.Workbench.Analytic.toNormalForm`
- **Reason:** Analytic normal form not implemented (Phase 24 scaffold only).
- **Evidence:** `rh_testing/tested/mertens_equivalence/dashboard_artifact.txt`
- **Skeleton:** `projects/rh_demo/User_RH_MertensSkeleton.lean`

---

### 2) nyman_beurling
- **Claim:** RH ⇔ Nyman–Beurling criterion  
  *(functional-analytic approximation in L^2(0,1))*
- **Status:** FAILED
- **Failure Type:** Analytic infrastructure boundary
- **Failure Point:** `MiniProver.Workbench.Analytic.toNormalForm`
- **Reason:** Analytic normal form not implemented (Phase 24 scaffold only).
- **Evidence:** `rh_testing/tested/nyman_beurling/dashboard_artifact.txt`
- **Skeleton:** `rh_testing/skeletons/User_RH_NymanBeurlingSkeleton.lean`

---

### 3) pnt_error_chebyshev_psi
- **Claim:** RH ⇒ Chebyshev psi error term  
  *(ψ(x) = x + O(√x · log^2 x))*
- **Status:** FAILED
- **Failure Type:** Analytic boundary (not formal / not logical)
- **Failure Point:** `MiniProver.Workbench.Analytic.toNormalForm`
- **Reason:** Reduction RH → ψ(x) error bound verified structurally via Lean obligation skeleton.  
  Analytic layer not implemented (explicit formula + zero-sum bounds + remainder control; obligations C3–C5).
- **Evidence:** `rh_testing/tested/pnt_error_chebyshev_psi/dashboard_artifact.txt`
- **Skeleton:** `rh_testing/skeletons/User_RH_Consequence_PNT_Psi.lean`

---

## Bucket Index (focus views; pointers only)

- **consequences_must_true**
  - `mertens_equivalence` → `rh_testing/tested/mertens_equivalence/`
  - `pnt_error_chebyshev_psi` → `rh_testing/tested/pnt_error_chebyshev_psi/`

- **incompatibles_must_false**
  - *(none)*

- **questionable**
  - `nyman_beurling` → `rh_testing/tested/nyman_beurling/`
