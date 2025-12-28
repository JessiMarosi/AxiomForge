# Axiom Forge — RH Testing Compilation Summary
**Generated:** 2025-12-28  
**Policy:** deterministic, auditable, no speculation

## Counts
- **TESTED:** 2  
- **FAILED:** 2  
- **PASSED:** 0  

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

### 2) nyman_beurling
- **Claim:** RH ⇔ Nyman–Beurling criterion  
  *(functional-analytic approximation in L^2(0,1))*
- **Status:** FAILED
- **Failure Type:** Analytic infrastructure boundary
- **Failure Point:** `MiniProver.Workbench.Analytic.toNormalForm`
- **Reason:** Analytic normal form not implemented (Phase 24 scaffold only).
- **Evidence:** `rh_testing/tested/nyman_beurling/dashboard_artifact.txt`
- **Skeleton:** `rh_testing/skeletons/User_RH_NymanBeurlingSkeleton.lean`
