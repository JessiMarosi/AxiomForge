import Mathlib
import MiniProver.Core

def main : IO Unit := do
  IO.println "mini_prover built; proofs verified."

example : (0 : Nat) < 1 := by
  decide
