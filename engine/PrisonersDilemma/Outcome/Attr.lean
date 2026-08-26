import Lean

/-!
# The `@[outcome]` attribute

Records which theorems claim to be outcome-matrix cells. Validation lives in
`Outcome/Lint.lean` and serialization in `Outcome/Export.lean` — this module only
maintains the list.

It is a SEPARATE module from both of those because Lean cannot evaluate an `initialize`
block in the module that declares it ("cannot evaluate `[init]` declaration … in the same
module"), so the attribute must be declared here and consumed elsewhere.
-/

open Lean

namespace PD.Outcome

/-- Mark a theorem as an outcome-matrix cell.

    Tagging is OPT-IN, which inverts the previous name-regex policy: an untagged
    `outcome_X_vs_Y` theorem is invisible to the matrix. `Outcome/Lint.lean`'s census is
    what stops that from failing silently — it errors on any cell-shaped declaration
    that is not tagged.

    Implemented with `registerTagAttribute` rather than a hand-rolled environment
    extension: the tag attribute's `PersistentEnvExtension` is already wired to write its
    entries into the `.olean`. A hand-rolled `SimplePersistentEnvExtension` looked correct
    and worked for the in-process linter, but its entries did NOT survive an import, so
    `lake exe export_outcomes` silently wrote zero cells. -/
initialize outcomeAttr : TagAttribute ←
  registerTagAttribute `outcome
    "outcome-matrix cell; validated by #check_outcome_theorems"

/-- Mark a theorem as a tau BIT ROW (`Tau/RowSpec.lean`); validated by `#check_tau_rows`
    (`Tau/Lint.lean`), exported to `app/generated/tau_rows.json`. -/
initialize tauRowAttr : TagAttribute ←
  registerTagAttribute `tau_row
    "tau bit row; validated by #check_tau_rows"

/-- Every tagged declaration, sorted for a deterministic export.

    `getState` alone returns ONLY the module currently being elaborated — imported tags
    live per-module and must be read with `getModuleEntries`. Reading just the state
    silently yields 0 tags everywhere except the defining module, which looks exactly
    like "nobody tagged anything" rather than like a bug. -/
def taggedBy (attr : TagAttribute) (env : Environment) : Array Name := Id.run do
  let mut out := (attr.ext.getState env).toArray
  for i in [0 : env.header.moduleNames.size] do
    out := out ++ attr.ext.getModuleEntries env i
  return out.qsort (·.toString < ·.toString)

def taggedOutcomes (env : Environment) : Array Name := taggedBy outcomeAttr env
def taggedTauRows (env : Environment) : Array Name := taggedBy tauRowAttr env

end PD.Outcome
