import ArithS.Tau.Columns
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.CupodTroll — τ(CupodTrollBot)'s row in PA-`S'`

τ(CupodTroll)'s instance at `T` is one `proveEq` stage on an INDEX-decided identity (`Tau/Spec.lean`): at the one
hypothesis it recognises the guard is the decidably true `.eq (.const C) (.const C)` — a `TAct`-theorem, found at
every large budget (`eq_const_found`), D; everywhere else it is the decidably false `.eq (.const C) (.const D)`
— never found (`eq_const_not_found`), C. Engine twin: `Tau/Theorems/TauCupodTroll/Phase.lean`
(`cupodTrollRowSpec`); every slot agrees.

**Floor bits** (`‡`, four): `dupoc`, `cimcic`, `maxconfidence`, `minconfidence` — all settled on this side (the
identity is false, SND); the hinge is the partner searcher's guard about CupodTroll's instance (base
`dich_DupocBot_vs_CupodTrollBot`, `dich_CIMCIC_vs_CupodTrollBot`), the open question on the partner's bit.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open PD PD.Tau

/-- τ(CupodTroll)'s bit row: D at the one hypothesis it recognises, C elsewhere. -/
def cupodTrollRowA : Tmpl → Action
  | .cupod => .D
  | _ => .C

/-- At every hypothesis but `cupod` the identity is false: C at every budget. -/
theorem cupodTroll_C (k : ℕ) (T : Tmpl) (h : T ≠ .cupod) : bitPlays k .cupodTroll T .C :=
  bit_search_not_found k (instCode_cupodTroll k T h) (fun me opp ↦ eq_const_not_found (by decide) me opp k)
    (fun _ _ ↦ const_play 0 _ _ _)

/-- At `cupod` the identity is a `TAct`-theorem: D for all large budgets. -/
theorem cupodTroll_cupod_D : bitEventually .cupodTroll .cupod .D :=
  bit_search_found instCode_cupodTroll_cupod (eq_const_found .C) (fun _ _ ↦ const_play 0 _ _ _)

/-- **τ(CupodTroll)'s row in `S'`** — 10 of the 14 paper slots (4 floor bits below). -/
@[tau_rowA]
theorem cupodTrollRowSpecA : RowSpecA .cupodTroll
    [.coop, .defect, .tftSim, .ebot, .obot, .dbot, .cupodTroll, .cupod, .dimcid, .prudent] cupodTrollRowA :=
  RowSpecA.cons (bitEventually.of_forall fun k ↦ cupodTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ cupodTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ cupodTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ cupodTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ cupodTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ cupodTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ cupodTroll_C k _ (by decide)) <|
  RowSpecA.cons cupodTroll_cupod_D <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ cupodTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ cupodTroll_C k _ (by decide)) <|
  RowSpecA.nil _ _

/-! ### The floor bits — settled on this side, the partner's hinge -/

/-- `cupodTroll × dupoc` ‡ (base `dich_DupocBot_vs_CupodTrollBot`): the identity is false — C. Hinge: Dupoc's
probe of CupodTroll's instance, in Dupoc's own frame. -/
@[tau_floor_bitA]
theorem cupodTrollRowSpecA_dupoc_floor : FloorBitA .cupodTroll .dupoc
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .cupodTroll .dupoc)))
      (pBot (instCode k .dupoc .cupodTroll)) (pBot (instCode k .dupoc .cupodTroll)) k)) .C :=
  FloorBitA.of _ (bitEventually.of_forall fun k ↦ cupodTroll_C k _ (by decide))

/-- `cupodTroll × cimcic` ‡ (base `dich_CIMCIC_vs_CupodTrollBot`): C. Hinge: CIMCIC's implication guard about
CupodTroll's instance, in CIMCIC's own frame. -/
@[tau_floor_bitA]
theorem cupodTrollRowSpecA_cimcic_floor : FloorBitA .cupodTroll .cimcic
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (inst (tauZoo k) .cupodTroll .cimcic)) .C)
      (.plays (.bot (inst (tauZoo k) .cupodTroll .cimcic)) .self .C)))
      (pBot (instCode k .cimcic .cupodTroll)) (pBot (instCode k .cimcic .cupodTroll)) k)) .C :=
  FloorBitA.of _ (bitEventually.of_forall fun k ↦ cupodTroll_C k _ (by decide))

/-- `cupodTroll × maxconfidence` ‡ (Dupoc's row by the bridge): C. -/
@[tau_floor_bitA]
theorem cupodTrollRowSpecA_maxconfidence_floor : FloorBitA .cupodTroll .maxconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .cupodTroll .maxconfidence)))
      (pBot (instCode k .maxconfidence .cupodTroll)) (pBot (instCode k .maxconfidence .cupodTroll)) k)) .C :=
  FloorBitA.of _ (bitEventually.of_forall fun k ↦ cupodTroll_C k _ (by decide))

/-- `cupodTroll × minconfidence` ‡ (Dupoc's row by the bridge): C. -/
@[tau_floor_bitA]
theorem cupodTrollRowSpecA_minconfidence_floor : FloorBitA .cupodTroll .minconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .cupodTroll .minconfidence)))
      (pBot (instCode k .minconfidence .cupodTroll)) (pBot (instCode k .minconfidence .cupodTroll)) k)) .C :=
  FloorBitA.of _ (bitEventually.of_forall fun k ↦ cupodTroll_C k _ (by decide))

end ArithS.Tau
