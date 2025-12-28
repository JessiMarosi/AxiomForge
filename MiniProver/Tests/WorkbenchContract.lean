import MiniProver.Workbench

/-
Phase 14 — Workbench API Contract Tests
Step 1 (Positive): The public entrypoint must import cleanly.

This file intentionally contains no new math.
It exists to lock the stability of `import MiniProver.Workbench`.
-/
namespace MiniProver.Tests

-- If this compiles, the contract holds at minimum: Workbench is import-stable.
theorem workbench_import_contract : True := by
  trivial

end MiniProver.Tests
