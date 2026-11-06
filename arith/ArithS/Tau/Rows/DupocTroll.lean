import ArithS.Tau.Columns
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.DupocTroll — τ(DupocTrollBot)'s row in PA-`S'` (2026-10-19)

The twin of `Rows/CupodTroll.lean` for the Dupoc-hunting identity checker (`Bots/DupocTrollBot.lean`, the
`S'`-only troll of the ladder zoo `body8+trolls`). τ(DupocTroll)'s instance at `T` is one `proveEq` stage on
a SOURCE-decided identity (`Tau/Spec.lean`, source equality since 2026-10-19): at a hypothesis whose spec is
Dupoc's — `.dupoc` itself and the two natives, which ARE Dupoc as hypotheses — the guard is the decidably
true `.eq (.const C) (.const C)`, a `TAct`-theorem found at every large budget (`eq_const_found`), D;
everywhere else it is the decidably false `.eq (.const C) (.const D)` — never found (`eq_const_not_found`),
C. Engine twin: `Tau/Theorems/TauDupocTroll/Phase.lean` (`dupocTrollRowSpec`); every slot agrees.

**Floor bit** (`‡`, one): `cimcic` — settled on this side (the identity is false, SND, C); the hinge is
CIMCIC's implication guard about the troll's instance (base `dich_DupocTrollBot_vs_CIMCIC`), the open
question on CIMCIC's bit. Unlike CupodTroll, the troll's bits against Dupoc and the natives are NOT floors
on either side: the troll DEFECTS on them, so their probe of it is false outright (`dupoc_dupocTroll_D`).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open PD PD.Tau

/-- τ(DupocTroll)'s bit row: D at the hypotheses with Dupoc's source, C elsewhere. -/
def dupocTrollRowA : Tmpl → Action
  | .dupoc | .maxconfidence | .minconfidence => .D
  | _ => .C

/-- **τ(DupocTroll)'s row in `S'`** — 15 of the 16 paper slots (the `cimcic` floor bit below). -/
@[tau_rowA]
theorem dupocTrollRowSpecA : RowSpecA .dupocTroll
    [.coop, .defect, .tftSim, .dupoc, .ebot, .obot, .dbot, .cupodTroll, .dupocTroll, .cupod, .dimcid, .dimdid,
     .prudent, .maxconfidence, .minconfidence] dupocTrollRowA :=
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dupocTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dupocTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dupocTroll_C k _ (by decide)) <|
  RowSpecA.cons (dupocTroll_rec_D _ rfl) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dupocTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dupocTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dupocTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dupocTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dupocTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dupocTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dupocTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dupocTroll_C k _ (by decide)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dupocTroll_C k _ (by decide)) <|
  RowSpecA.cons (dupocTroll_rec_D _ rfl) <|
  RowSpecA.cons (dupocTroll_rec_D _ rfl) <|
  RowSpecA.nil _ _

/-! ### The floor bit — settled on this side, the partner's hinge -/

/-- `dupocTroll × cimcic` ‡ (base `dich_DupocTrollBot_vs_CIMCIC`): the identity is false — C. Hinge: CIMCIC's
implication guard about the troll's instance, in CIMCIC's own frame. -/
@[tau_floor_bitA]
theorem dupocTrollRowSpecA_cimcic_floor : FloorBitA .dupocTroll .cimcic
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (inst (tauZoo k) .dupocTroll .cimcic)) .C)
      (.plays (.bot (inst (tauZoo k) .dupocTroll .cimcic)) .self .C)))
      (pBot (instCode k .cimcic .dupocTroll)) (pBot (instCode k .cimcic .dupocTroll)) k)) .C :=
  FloorBitA.of _ (bitEventually.of_forall fun k ↦ dupocTroll_C k _ (by decide))

end ArithS.Tau
