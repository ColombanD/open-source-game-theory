import ArithS.Outcome.Attr

/-!
# ArithS.Tau.Attr — the `@[tau_rowA]` and `@[tau_floor_bitA]` attributes

The tau twin of `Outcome/Attr.lean`: `@[tau_rowA]` marks a template's row theorem (`RowSpecA`, `Tau/Spec.lean`)
and `@[tau_floor_bitA]` one floor bit (`FloorBitA`). Validation is `Tau/Lint.lean`, serialization
`Outcome/Export.lean` (`app/generated/sprime_tau_rows.json`); this module only maintains the lists, in its own
module because an `initialize` block cannot be evaluated by the module that declares it. Design note:
`Research/Notes/SPRIME_SOURCE_OF_TRUTH.md` §3 (the Phase 3 contract).

Both are `registerTagAttribute`s (a hand-rolled extension's entries do not survive an import — the engine's
incident, `Outcome/Attr.lean`); the tags are read with `taggedBy`, which walks the imported modules' entries.
-/

open Lean

namespace ArithS.Tau

/-- Mark a theorem as a PA-`S'` tau bit ROW (`RowSpecA .<t> <order> <t>RowA`); validated by `#check_tau_rowsA`. -/
initialize tauRowAAttr : TagAttribute ←
  registerTagAttribute `tau_rowA
    "PA-S' tau bit row; validated by #check_tau_rowsA"

/-- Mark a theorem as a PA-`S'` tau FLOOR BIT (`FloorBitA .<t> .<T> (fun k ↦ …) a`, named `<t>RowSpecA_<T>_floor`);
validated by `#check_tau_rowsA`. -/
initialize tauFloorBitAAttr : TagAttribute ←
  registerTagAttribute `tau_floor_bitA
    "PA-S' tau floor bit (the engine-side half of a base dichotomy on one bit); validated by #check_tau_rowsA"

def taggedTauRowsA (env : Environment) : Array Name := ArithS.Outcome.taggedBy tauRowAAttr env
def taggedTauFloorBitsA (env : Environment) : Array Name := ArithS.Outcome.taggedBy tauFloorBitAAttr env

end ArithS.Tau
