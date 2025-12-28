/-
MiniProver.Workbench — Public, stable API surface.

Policy:
- Downstream modules should import `MiniProver.Workbench` (preferred) or a specific Workbench module.
- Do NOT import `MiniProver.Library.*` directly from downstream code.
- Workbench re-exports stable tools only; internals may change without notice.
-/
import MiniProver.Workbench.ModEq

import MiniProver.Workbench.Assumptions

import MiniProver.Workbench.Dashboard
