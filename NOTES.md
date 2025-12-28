# Axiom Forge — Working Notes

## Phase 1 — Non-Goals (LOCKED)

We are NOT doing these yet (they are deferred to future phases):

1. Attempting to formalize or prove/disprove the Riemann Hypothesis.
2. Building an "automatic theorem prover" beyond Lean's standard elaboration + tactics.
3. Adding AI/LLM assistance, web access, or any non-deterministic component.
4. Writing large narrative documentation; only breadcrumbs at conceptual forks.
5. Refactoring for performance unless it blocks correctness or determinism.
6. Adding external tooling (parsers, exporters, UIs) unless required for a minimal proof pipeline.
7. Expanding into broad mathlib coverage; we will formalize only what we actively use.

## Phase 1 — Minimal Formal Target

Goal:
Establish a clean end-to-end formalization pipeline by stating and proving
a small, nontrivial but well-known result from mathlib without inventing new theory.

Initial target:
- Use an existing definition already present in mathlib (e.g., parity, divisibility,
  or an order-related property on ℕ or ℤ).
- State one basic lemma about this definition.
- Prove it using standard Lean tactics.
- Place the definition and proof in MiniProver/Core.lean.

Success criteria:
- Imports are minimal and explicit.
- No name collisions with mathlib.
- Proof is readable, deterministic, and reproducible.
- `lake build` succeeds with no warnings.

Non-criteria:
- Mathematical novelty.
- Performance optimization.
- Proof elegance beyond clarity.

Purpose:
This file records brief human notes at major decision points
to preserve intent and reasoning that are not captured by formal proofs.

Guidelines:
- Write notes only at conceptual forks, reductions, or abandoned paths.
- Keep entries short (2–10 lines).
- Do not attempt to narrate every proof step.
- Informal notes do not override formal verification.

Format (optional):
- Date
- Context (file / section)
- Decision and rationale

## Phase 2 — Equivalence Layer (LOCKED)

Proved mp_even_iff_even : MP_Even n ↔ Even n in MiniProver/Core.lean.
Confirmed deterministic builds: lake build MiniProver.Core and full lake build succeed.

## Phase 3 — Rewrite Bridge Usage (LOCKED)

Added mp_even_add_of_mp_even : MP_Even m -> MP_Even n -> MP_Even (m + n) by rewriting MP_Even <-> Even using mp_even_iff_even and reusing even_add_of_even.
Confirmed deterministic builds: lake build MiniProver.Core and full lake build succeed.

## Phase 4 — Module Discipline Test (LOCKED)

Added MiniProver/Bridge.lean importing MiniProver.Core and proving bridge_mp_even_add via Core exports.
Confirmed deterministic builds: lake build MiniProver.Bridge and full lake build succeed.


## Phase 5 — Reproducible Clean Build (LOCKED)

Added scripts/clean_build.sh to remove .lake/build and rebuild deterministically.
Verified clean rebuild succeeded: ./scripts/clean_build.sh (full lake build).

## Phase 6 — Controlled Problem Validation (Test 1 LOCKED)

Added MiniProver/Tests/EvenClosure.lean proving mp_even_mul_right: MP_Even m -> MP_Even (m * n) via mp_even_iff_even and mathlib Even.mul_right.
Confirmed deterministic builds: lake build MiniProver.Tests.EvenClosure and full lake build succeed.

## Phase 6 — Controlled Problem Validation (Test 2 LOCKED)

Added MiniProver/Tests/BridgeReuse.lean proving test_bridge_add via MiniProver.Bridge (Tests -> Bridge -> Core reuse).
Confirmed deterministic builds: lake build MiniProver.Tests.BridgeReuse and full lake build succeed.

## Phase 6 — Controlled Problem Validation (Test 3 LOCKED)

Added MiniProver/Tests/Negative.lean using fail_if_success to confirm a false claim (MP_Even 1 via k=0) is not provable, while the module still compiles.
Confirmed deterministic builds: lake build MiniProver.Tests.Negative and full lake build succeed.

## Phase 7 — Odd Predicate + Transport (LOCKED)

Added MP_Odd and proved mp_odd_iff_odd : MP_Odd n ↔ Odd n in MiniProver/Core.lean.
Added operational lemma mp_odd_add_of_mp_odd_mp_even transporting MP_Odd/MP_Even through Odd/Even and reusing Odd.add_even.
Confirmed deterministic builds: lake build MiniProver.Core and full lake build succeed.

## Phase 8 — Mod 2 Parity Calibration (LOCKED)

Added MiniProver/Tests/Mod2.lean proving even_iff_mod2_eq_zero using Nat.even_iff, and lifted to mp_even_iff_mod2_eq_zero via mp_even_iff_even.
Confirmed deterministic builds: lake build MiniProver.Tests.Mod2 and full lake build succeed.

## Phase 9 — Mod 2 Odd Calibration (LOCKED)

Added MiniProver/Tests/Mod2Odd.lean proving odd_iff_mod2_eq_one using Nat.odd_iff, and lifted to mp_odd_iff_mod2_eq_one via mp_odd_iff_odd.
Confirmed deterministic builds: lake build MiniProver.Tests.Mod2Odd and full lake build succeed.

## Phase 10 — Modular Arithmetic (ModEq Basics Test 1 LOCKED)

Added MiniProver/Tests/ModEqBasics.lean proving modeq_add_right: a ≡ b [MOD n] -> a+c ≡ b+c [MOD n] via Nat.ModEq.add_right.
Confirmed deterministic builds: lake build MiniProver.Tests.ModEqBasics and full lake build succeed.

## Phase 10 — Modular Arithmetic (ModEq Basics Test 2 LOCKED)

Added MiniProver/Tests/ModEqMul.lean proving modeq_mul_right: a ≡ b [MOD n] -> a*c ≡ b*c [MOD n] via Nat.ModEq.mul_right.
Confirmed deterministic builds: lake build MiniProver.Tests.ModEqMul and full lake build succeed.

## Phase 10 — Modular Arithmetic (ModEq Algebra LOCKED)

Added MiniProver/Tests/ModEqAlgebra.lean locking core properties: modeq_refl, modeq_symm, modeq_trans.
Confirmed deterministic builds: lake build MiniProver.Tests.ModEqAlgebra and full lake build succeed.

## Phase 11 — ModEq ↔ % (Computational View) (Step 1 LOCKED)

Added MiniProver/Tests/ModEqMod.lean proving Nat.ModEq n a b ↔ a % n = b % n via rfl.
Builds: lake build MiniProver.Tests.ModEqMod succeeds.

## Phase 11 — ModEq ↔ % (Computational View) (Step 2 LOCKED)

Added MiniProver/Tests/ModEqModAlgebra.lean proving computational closure under + and * (remainder-equality view), using Nat.ModEq.add_right and Nat.ModEq.mul_right via the Step 1 bridge.
Builds: lake build MiniProver.Tests.ModEqModAlgebra succeeds.

## Phase 11 — ModEq ↔ dvd (Arithmetic View) (Step 3 LOCKED)

Added MiniProver/Tests/ModEqDvdBridge.lean proving Nat.ModEq n a b ↔ (n : Int) ∣ (b : Int) - (a : Int) using Nat.modEq_iff_dvd.
Builds: lake build MiniProver.Tests.ModEqDvdBridge succeeds.

## Phase 11 — ModEq Canonical Representative (Step 4 LOCKED)

Added MiniProver/Tests/ModEqCanonical.lean proving a ≡ a % n [MOD n] via the % bridge and Nat.mod_mod, and proving canonical uniqueness (ModEq → equal remainders).
Builds: lake build MiniProver.Tests.ModEqCanonical succeeds.

## Phase 11 — ModEq Linear Form (Step 5 LOCKED)

Added MiniProver/Tests/ModEqLinearForm.lean proving:
Nat.ModEq n a b ↔ ∃ z : Int, (b : Int) = (a : Int) + (n : Int) * z
Derived from Step 3 theorem modeq_iff_int_dvd_int_sub by algebraic rearrangement.
Build: lake build MiniProver.Tests.ModEqLinearForm succeeds.

## Phase 12 — ModEq Add-Cancellation (Step 1 LOCKED)

Added MiniProver/Tests/ModEqAddCancel.lean proving:
Nat.ModEq n (a + c) (b + c) ↔ Nat.ModEq n a b
Backward direction via add_right; forward direction via Step 3 (Int dvd of subtraction) and cancellation.
Build: lake build MiniProver.Tests.ModEqAddCancel succeeds.

## Phase 12 — ModEq Add-Shift (Step 2 LOCKED)

Added MiniProver/Tests/ModEqAddShift.lean proving:
Nat.ModEq n a b ↔ Nat.ModEq n (a + c) (b + c)
Forward via add_right; backward via Phase 12 Step 1 cancel-iff.
Build: lake build MiniProver.Tests.ModEqAddShift succeeds.

## Phase 12 — ModEq Mul-Cancellation (Scaled Modulus, Nonzero Gate) (Step 3 LOCKED)

Added MiniProver/Tests/ModEqMulCancelCoprime.lean proving scaled-modulus cancellation:
(1) Nat.ModEq (c * m) (c * a) (c * b) → Nat.ModEq m a b, assuming c ≠ 0
(2) Nat.ModEq (m * c) (a * c) (b * c) → Nat.ModEq m a b, assuming c ≠ 0
Derived directly from mathlib lemmas Nat.ModEq.mul_left_cancel' and Nat.ModEq.mul_right_cancel'.
Build: lake build MiniProver.Tests.ModEqMulCancelCoprime succeeds.

## Phase 12 — ModEq Coprime Product Modulus (Step 4 LOCKED)

Added MiniProver/Tests/ModEqCoprimeMulIff.lean proving:
(Nat.ModEq m a b ∧ Nat.ModEq n a b) ↔ Nat.ModEq (m * n) a b, assuming Nat.Coprime m n
Wrapper around mathlib theorem Nat.modEq_and_modEq_iff_modEq_mul.
Build: lake build MiniProver.Tests.ModEqCoprimeMulIff succeeds.

## Phase 12 — Chinese Remainder Existence (Step 5 LOCKED)

Added MiniProver/Tests/ModEqChineseRemainderExists.lean proving:
∃ k, k ≡ a [MOD n] ∧ k ≡ b [MOD m], assuming Nat.Coprime n m
Wrapper around mathlib construction Nat.chineseRemainder.
Build: lake build MiniProver.Tests.ModEqChineseRemainderExists succeeds.

## Phase 13 — ModEq Normalize Chain Negative (Step 2 LOCKED)

Added MiniProver/Tests/ModEqNormalizeChainNegative.lean as a guardrail negative test:
Attempts to derive Nat.ModEq n a c from hab : Nat.ModEq n a b and hbc : Nat.ModEq (n+1) b c.
Wrapped the failing attempt in fail_if_success (from MiniProver.Tests.Negative) so the file compiles.
Build: lake build MiniProver.Tests.ModEqNormalizeChainNegative succeeds.

## Phase 13 — ModEq Workbench Pack (Step 3 LOCKED)

Added MiniProver/Workbench/ModEq.lean as a stable import module re-exporting the most-used ModEq tools (Phases 11–13, Phase 12).
Build: lake build MiniProver.Workbench.ModEq succeeds.

## Phase 13 — ModEq Workbench Pack (Step 4 LOCKED)

Updated MiniProver/Workbench/ModEq.lean with stable wrapper lemma names (aliases via simpa) around LOCKED ModEq tools (Phases 11–13, Phase 12).
Build: lake build MiniProver.Workbench.ModEq succeeds.

## Phase 13 — Dependency Hygiene (Step 5.4 LOCKED)

Fixed structural scope error in MiniProver/Workbench/ModEq.lean (removed orphaned docstring causing unexpected ). Target build: lake build MiniProver.Workbench.ModEq succeeds.

## Phase 13 — Dependency Hygiene (Step 5.5 LOCKED)

Created MiniProver/Library as the non-test home for ModEq lemma modules (moved 11 ModEq*.lean files from MiniProver/Tests to MiniProver/Library). Reintroduced MiniProver/Tests forwarder stubs to preserve legacy import paths. Updated MiniProver/Workbench/ModEq.lean to import MiniProver/Library (not MiniProver/Tests). Verified builds: lake build MiniProver.Workbench.ModEq and lake build MiniProver.Tests.ModEqCanonical succeed.

## Phase 13 — Workbench Consolidation & Export Discipline (Step 6 LOCKED)

Eliminated remaining layer inversion: MiniProver/Library imports no MiniProver/Tests modules (internal imports repointed to MiniProver/Library equivalents). Verified only Workbench and Tests-forwarders import Library. Downstream modules should import MiniProver.Workbench.ModEq as the stable API.
Builds: lake build MiniProver.Workbench.ModEq and full lake build succeed.

## Phase 13 — Public API Entrypoint (Step 7 LOCKED)

Added MiniProver/Workbench.lean as the canonical stable import surface (re-exporting MiniProver.Workbench.ModEq). Verified no downstream modules import MiniProver.Library.* directly (only Workbench and Tests forwarders). Builds: lake build MiniProver.Workbench and full lake build succeed.

## Phase 13 — Library Namespace Hygiene (Step 8 LOCKED)

Moved ModEq lemma declarations in MiniProver/Library from namespace MiniProver.Tests to MiniProver.Library (matching file location). Updated MiniProver/Workbench/ModEq wrappers to reference MiniProver.Library.* names. Verified builds: lake build MiniProver.Workbench.ModEq, lake build MiniProver.Workbench, and full lake build succeed.

## Phase 13 — Tests Forwarder Deprecation Notes (Step 9 LOCKED)

Annotated MiniProver/Tests ModEq* forwarder stubs as compatibility-only modules (policy header + single import), clarifying Workbench as the preferred stable API and Library as internal. Verified builds remain deterministic.

## Phase 14 — Workbench API Contract Tests (Steps 1–3 LOCKED)

Step 1: Added MiniProver/Tests/WorkbenchContract.lean as a positive contract test ensuring `import MiniProver.Workbench` always succeeds.
Step 2 (Revised/enforceable): Introduced deterministic import policy gate via `import_gate` executable to forbid direct `MiniProver.Tests/*` → `MiniProver.Library.*` imports.
Step 3: Added scripts/policy_check.sh to run `lake build` + import gate; confirmed output: import_gate: OK, policy_check: OK.
Builds verified deterministic.


## Phase 15 — Deterministic normal-form automation scaffold (Steps 1–3 LOCKED)

Step 1: Added `MiniProver.Workbench.Normalize` as a stable public namespace for future deterministic normal-form passes (no automation yet; identity placeholder).
Step 2: Stabilized `Normalize.normalize` signature as `normalize (x) (_cfg := {})` and kept definitional identity.
Step 3: Added downstream consumer contract test `MiniProver/Tests/NormalizeContract.lean` proving `Normalize.normalize` is definitional identity (`rfl`).
Policy gate + deterministic rebuild verified via `./scripts/policy_check.sh` (import_gate: OK, policy_check: OK).


## Phase 16 — Contract + lint policy gates (LOCKED)

Added generalized import policy enforcement:
- Tests must not import `MiniProver.Library.*`
- Workbench must not import `MiniProver.Tests.*`
- Library must not import `MiniProver.Tests.*`

Wired all import policies into a single authoritative command:
`./scripts/policy_check.sh`

Confirmed deterministic rebuilds and policy enforcement:
import_policy_check: OK
policy_check: OK


## Phase 17 — Boundary & negative-test expansion (Steps 1–2 LOCKED)

Step 1: Introduced intentional negative-test artifacts to validate import policy enforcement:
- Forbidden: Tests → Library import
- Forbidden: Workbench → Tests import
- Forbidden: Library → Tests import

Confirmed that `./scripts/policy_check.sh` correctly failed with explicit file/line diagnostics.

Step 2: Removed all forbidden artifacts and re-ran policy checks.
Confirmed deterministic recovery:
- import_gate: OK
- import_policy_check: OK
- policy_check: OK
Builds verified deterministic.


## Phase 18 — Proof skeleton emission (Steps 1–2 LOCKED)

Step 1: Added `MiniProver.Workbench.Skeleton` defining a minimal, deterministic proof-skeleton representation:
- `Obligation` (named goal)
- `ProofSkeleton` (assumptions + obligations)
- `Skeleton.empty` (baseline constructor)

Step 2: Added downstream consumer contract test `MiniProver/Tests/SkeletonContract.lean` asserting `Skeleton.empty` fields are definitionally empty (`rfl`).

Policy enforcement + deterministic rebuild verified via `./scripts/policy_check.sh`:
import_policy_check: OK
policy_check: OK


## Phase 21 — Typed formulation registry + assumption ledger (Steps 1–4 LOCKED)

Step 1: Added `MiniProver.Workbench.Formulation` defining a minimal typed formulation record (`FormulationId`, `Formulation`, helper `Formulation.ofStmt`).
Step 2: Added downstream consumer contract test `MiniProver/Tests/FormulationContract.lean` proving `Formulation.ofStmt` is definitional (`rfl`).
Step 3: Added `MiniProver.Workbench.Assumptions` defining named assumption entries and `AssumptionLedger`, and wired `ProofSkeleton.assumptions` to use the ledger.
Step 4: Added downstream consumer contract test `MiniProver/Tests/AssumptionsContract.lean` proving `Assumptions.empty` and `Skeleton.empty.assumptions` are definitional (`rfl`).
Policy enforcement + deterministic rebuild verified via `./scripts/policy_check.sh`:
import_policy_check: OK
policy_check: OK


## Phase 22 — Reduction engine + obligation compiler pass (Steps 1–2 LOCKED)

Step 1: Added `MiniProver.Workbench.Reduction` defining `ReductionStep` linking:
- source formulation → destination formulation
- explicit `AssumptionLedger`
- embedded `ProofSkeleton` (obligations)

Provided deterministic accessors:
- `Reduction.compile` returns the embedded skeleton
- `Reduction.ledger` returns the embedded ledger

Step 2: Added downstream consumer contract test `MiniProver/Tests/ReductionContract.lean` constructing a trivial `ReductionStep` and proving `Reduction.compile` is definitional (`rfl`).

Policy enforcement + deterministic rebuild verified via `./scripts/policy_check.sh`:
import_policy_check: OK
policy_check: OK


## Phase 23 — Failure & boundary surfacing (Steps 1–3 LOCKED)

Step 1: Added `MiniProver.Workbench.Failure` defining:
- `FailureKind` (deterministic categories)
- `Failure` (kind + message + optional context)
- helper `Failure.withContext`

Step 2: Updated `Reduction.compile` to be total and failure-aware:
`compile : ReductionStep → Except Failure ProofSkeleton` (currently always `Except.ok`).

Step 3: Added `Reduction.validate : ReductionStep → Except Failure Unit` as a deterministic invariant hook (currently always `Except.ok`).

Updated downstream consumer contract test `MiniProver/Tests/ReductionContract.lean` to assert definitional behavior (`rfl`) for `validate` and `compile`.

Policy enforcement + deterministic rebuild verified via `./scripts/policy_check.sh`:
import_policy_check: OK
policy_check: OK


## Phase 24 — Analytic normal forms (Steps 1–2 LOCKED)

Step 1: Added `MiniProver.Workbench.Analytic` scaffold:
- `AnalyticNormalForm` placeholder type
- `Analytic.toNormalForm : Formulation → Except Failure AnalyticNormalForm` which deterministically returns `Except.error` (scaffold-only; prevents overclaiming)

Step 2: Added downstream consumer contract test `MiniProver/Tests/AnalyticContract.lean` asserting:
- `Analytic.toNormalForm` returns `Except.error`
- error kind is `FailureKind.internalInvariant`

Policy enforcement + deterministic rebuild verified via `./scripts/policy_check.sh`:
import_policy_check: OK
policy_check: OK


## Phase 25 — Guided interface / dashboard (Step 1 LOCKED)

Step 1: Added `MiniProver.Workbench.Dashboard`, a deterministic, text-only inspection layer:
- Pure `String` renderers for `Failure`, `AssumptionLedger`, `ProofSkeleton`, `ReductionStep`
- Safe summaries without rendering `Prop` contents
- Explicit surfacing of `compile`, `validate`, and analytic scaffold failures
- No IO, no UI frameworks, no nondeterminism

Added downstream consumer contract test `MiniProver/Tests/DashboardContract.lean` asserting:
- dashboard renderers are pure and total
- outputs are deterministic `String` values

Policy enforcement + deterministic rebuild verified via `./scripts/policy_check.sh`:
import_policy_check: OK
policy_check: OK


## Phases 19–20 — Reserved (Intentional)

Phases 19 and 20 are intentionally reserved as contingency buffer phases.

Purpose:
- Allow structural refactors discovered after proof-skeleton emission
- Preserve roadmap numbering stability without renumbering later phases
- Provide space for invariant tightening or redesign if Phase 21+ revealed architectural gaps

No work was omitted.
No capabilities were deferred without record.
The jump from Phase 18 → Phase 21 is intentional and documented.


## Phase 25 — End-user dashboard CLI (Views) (Step 3 LOCKED)

Added executable `axiom_dashboard` providing deterministic text dashboard views backed by
`MiniProver.Workbench.Dashboard`.

Implementation:
- `MiniProver/Tools/DashboardCli.lean`
- Uses Lake-native `main (args : List String)` (no `IO.getArgs` / `System.getArgs`)
- Supported views: `all`, `reduction`, `analytic`, `help`
- Output is stable and audit-friendly `String` renders from the Workbench layer

Verified:
- `lake build axiom_dashboard` succeeds
- `lake exe axiom_dashboard help|reduction|analytic` works as expected

