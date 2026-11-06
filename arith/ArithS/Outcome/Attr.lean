import Lean

/-!
# ArithS.Outcome.Attr — the `@[outcomeA]` and `@[floorA]` attributes

The PA-`S'` twin of the engine's `PrisonersDilemma/Outcome/Attr.lean`: records which theorems claim to be
`S'` matrix cells (`@[outcomeA]`, an `OutcomeSpecA` statement in `Outcome/Matrix/<L>.lean`) and which are the
engine-side half of a floor dichotomy (`@[floorA]`, a `FloorSpecA` statement in `Outcome/Floors.lean`).
Validation lives in `Outcome/Lint.lean` and serialization in `Outcome/Export.lean`; this module only maintains
the lists. Design note: `docs/notes/SPRIME_SOURCE_OF_TRUTH.md` §1.1.

It is a SEPARATE module from both of those because Lean cannot evaluate an `initialize` block in the module
that declares it, so the attribute must be declared here and consumed elsewhere. `Outcome/Spec.lean` stays free
of `import Lean`; the `Matrix/<L>.lean` files import this module for the tag.
-/

open Lean

namespace ArithS.Outcome

/-- Mark a theorem as an `S'` outcome-matrix cell (`OutcomeSpecA regime L R r`).

    Tagging is OPT-IN, as in the engine: an untagged `outcome_<L>_vs_<R>` theorem is invisible to the export.
    `Outcome/Lint.lean`'s census (`#check_outcomeA_theorems`) is what stops that from failing silently — it
    errors on any cell-shaped declaration under `Outcome/Matrix/` that is not tagged.

    Implemented with `registerTagAttribute` rather than a hand-rolled environment extension: the tag
    attribute's `PersistentEnvExtension` is already wired to write its entries into the `.olean`. A hand-rolled
    `SimplePersistentEnvExtension` looked correct and worked for the in-process linter, but its entries did NOT
    survive an import, so the exporter silently wrote zero cells (the engine's incident). -/
initialize outcomeAAttr : TagAttribute ←
  registerTagAttribute `outcomeA
    "PA-S' outcome-matrix cell; validated by #check_outcomeA_theorems"

/-- Mark a theorem as the ENGINE-SIDE HALF of a floor dichotomy (`FloorSpecA L R hinge r`): the cell's value
    under the negation of its hinge, the bounded-consistency question `S'` takes no side on
    (`Cells/FloorDichotomy.lean`). Named `outcome_<L>_vs_<R>_floor`, validated by `#check_floorA_theorems`,
    exported in the `floors` array with provenance `floor_dichotomy`. -/
initialize floorAAttr : TagAttribute ←
  registerTagAttribute `floorA
    "engine-side half of a PA-S' floor dichotomy; validated by #check_floorA_theorems"

/-- Every tagged declaration, sorted for a deterministic export.

    `getState` alone returns ONLY the module currently being elaborated — imported tags live per-module and
    must be read with `getModuleEntries`. Reading just the state silently yields 0 tags everywhere except the
    defining module, which looks exactly like "nobody tagged anything" rather than like a bug. -/
def taggedBy (attr : TagAttribute) (env : Environment) : Array Name := Id.run do
  let mut out := (attr.ext.getState env).toArray
  for i in [0 : env.header.moduleNames.size] do
    out := out ++ attr.ext.getModuleEntries env i
  return out.qsort (·.toString < ·.toString)

def taggedOutcomesA (env : Environment) : Array Name := taggedBy outcomeAAttr env
def taggedFloorsA (env : Environment) : Array Name := taggedBy floorAAttr env

end ArithS.Outcome
