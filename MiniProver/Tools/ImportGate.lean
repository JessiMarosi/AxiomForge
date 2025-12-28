import Std

namespace MiniProver.Tools.ImportGate

/--
A deterministic import gate implemented via local `grep`.

Usage:
  lake exe import_gate -- <rootDir> <forbiddenSubstring>

Behavior:
- Scans `<rootDir>` recursively for `.lean` files containing `<forbiddenSubstring>`.
- If any matches are found, prints them and exits with code 1 (policy FAIL).
- If no matches are found, prints OK and exits with code 0.
- If grep errors, exits with code 2.
-/
def run (args : List String) : IO UInt32 := do
  match args with
  | rootDir :: forbidden :: _ =>
      let script :=
        "set -euo pipefail; " ++
        -- grep exit codes:
        -- 0: matches found
        -- 1: no matches
        -- 2: error
        s!"grep -R -n --include='*.lean' {String.quote forbidden} {String.quote rootDir} || true"
      let out ← IO.Process.output {
        cmd := "bash"
        args := #["-lc", script]
      }

      -- `trimAscii` avoids deprecated `trim` and yields a String.Slice.
      -- We convert it back to String via `toString`.
      let trimmed : String := (out.stdout.trimAscii).toString

      if trimmed != "" then
        IO.eprintln out.stdout
        IO.eprintln s!"import_gate: FAILED (found forbidden pattern: {forbidden})"
        return 1
      else
        IO.println "import_gate: OK"
        return 0
  | _ =>
      IO.eprintln "Usage: lake exe import_gate -- <rootDir> <forbiddenSubstring>"
      return 2

end MiniProver.Tools.ImportGate

/-- Lake executable entrypoint (must be top-level). -/
def main (args : List String) : IO UInt32 :=
  MiniProver.Tools.ImportGate.run args
