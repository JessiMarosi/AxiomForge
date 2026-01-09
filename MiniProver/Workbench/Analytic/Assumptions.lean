namespace MiniProver.Workbench.Analytic

/-
Assumption Ledger (v1)

Purpose:
- Explicit, typed inventory of assumptions used by a formulation/proof path.
- Deterministic, audit-grade bookkeeping only.
- No mathematical truth is introduced here.

Design constraints:
- No heuristics
- No inference
- No automation guesses
- Stable identifiers (inductive tags)
- Deterministic rendering for dashboards/reports
-/

/-- High-level categories of assumptions a route may rely on. -/
inductive AssumptionTag : Type
  | classicalLogic          -- Classical reasoning (choice/EM), if explicitly used.
  | realAnalysis            -- Real analysis facts beyond basic definitions.
  | complexAnalysis         -- Complex analysis facts.
  | analyticNumberTheory    -- General analytic number theory toolbox.
  | zetaTheory              -- Facts about ζ(s) specifically.
  | primeNumberTheory       -- PNT-level facts and standard prime estimates.
  | asymptoticsBigO         -- Big-O/Theta framework assumptions.
  | summatoryFunctions      -- Facts about summatory arithmetic functions.
  | measureTheory           -- Measure/integration assumptions.
  | functionalAnalysis      -- Functional analysis assumptions.
  | bridgeAxiom             -- Declarative bridge placeholders (explicitly NOT proofs).
  | externalReference       -- Referenced-but-not-formalized facts.
  deriving Repr, DecidableEq

/-- Deterministic human-readable label for an assumption tag. -/
def AssumptionTag.label : AssumptionTag → String
  | .classicalLogic       => "classical_logic"
  | .realAnalysis         => "real_analysis"
  | .complexAnalysis      => "complex_analysis"
  | .analyticNumberTheory => "analytic_number_theory"
  | .zetaTheory           => "zeta_theory"
  | .primeNumberTheory    => "prime_number_theory"
  | .asymptoticsBigO      => "asymptotics_bigO"
  | .summatoryFunctions   => "summatory_functions"
  | .measureTheory        => "measure_theory"
  | .functionalAnalysis   => "functional_analysis"
  | .bridgeAxiom          => "bridge_axiom"
  | .externalReference    => "external_reference"

/--
Assumption ledger entry:
- `tag` = typed category
- `note` = short concrete justification (optional)
-/
structure AssumptionEntry where
  tag  : AssumptionTag
  note : String := ""
  deriving Repr, DecidableEq

/--
A formulation/proof-path assumption ledger.
Bookkeeping only; does not assert truth of any assumption.
-/
structure AssumptionLedger where
  entries : List AssumptionEntry := []
  deriving Repr, DecidableEq

namespace AssumptionLedger

/-- Empty ledger. -/
def empty : AssumptionLedger := ⟨[]⟩

/-- Add one entry. -/
def add (L : AssumptionLedger) (tag : AssumptionTag) (note : String := "") : AssumptionLedger :=
  ⟨{ tag := tag, note := note } :: L.entries⟩

/-- Internal: deterministically remove exact duplicates (tag+note). -/
private def dedupEntries (xs : List AssumptionEntry) : List AssumptionEntry :=
  let rec go (seen : List AssumptionEntry) (rest : List AssumptionEntry) : List AssumptionEntry :=
    match rest with
    | [] => seen.reverse
    | x :: xs =>
      if seen.contains x then go seen xs else go (x :: seen) xs
  go [] xs

/-- Merge two ledgers (deterministic; exact-duplicate removal only). -/
def merge (A B : AssumptionLedger) : AssumptionLedger :=
  ⟨dedupEntries (A.entries ++ B.entries)⟩

/-- Render a deterministic, audit-friendly multi-line string. -/
def render (L : AssumptionLedger) : String :=
  let lines :=
    (L.entries.map fun e =>
      if e.note.trim.isEmpty then
        s!"- {e.tag.label}"
      else
        s!"- {e.tag.label}: {e.note}")
  String.intercalate "\n" lines

end AssumptionLedger

end MiniProver.Workbench.Analytic
