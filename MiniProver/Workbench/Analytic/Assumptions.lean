namespace MiniProver.Workbench.Analytic

/-
Assumption Ledger (v1)

Purpose:
- Explicit, typed inventory of assumptions used by a formulation/proof path.
- Deterministic, audit-grade bookkeeping only.
- No mathematical truth is introduced here.
-/

inductive AssumptionTag : Type
  | classicalLogic
  | realAnalysis
  | complexAnalysis
  | analyticNumberTheory
  | zetaTheory
  | primeNumberTheory
  | asymptoticsBigO
  | summatoryFunctions
  | measureTheory
  | functionalAnalysis
  | bridgeAxiom
  | externalReference
  deriving Repr, DecidableEq

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

structure AssumptionEntry where
  tag  : AssumptionTag
  note : String := ""
  deriving Repr, DecidableEq

structure AssumptionLedger where
  entries : List AssumptionEntry := []
  deriving Repr, DecidableEq

namespace AssumptionLedger

def empty : AssumptionLedger := ⟨[]⟩

def add (L : AssumptionLedger) (tag : AssumptionTag) (note : String := "") : AssumptionLedger :=
  ⟨{ tag := tag, note := note } :: L.entries⟩

private def dedupEntries (xs : List AssumptionEntry) : List AssumptionEntry :=
  let rec go (seen : List AssumptionEntry) (rest : List AssumptionEntry) :=
    match rest with
    | [] => seen.reverse
    | x :: xs =>
      if seen.contains x then go seen xs else go (x :: seen) xs
  go [] xs

def merge (A B : AssumptionLedger) : AssumptionLedger :=
  ⟨dedupEntries (A.entries ++ B.entries)⟩

def render (L : AssumptionLedger) : String :=
  let lines :=
    L.entries.map fun e =>
      if e.note.trimAscii.isEmpty then
        s!"- {e.tag.label}"
      else
        s!"- {e.tag.label}: {e.note}"
  String.intercalate "\n" lines

end AssumptionLedger
end MiniProver.Workbench.Analytic
