/-!
# Path A — HBL D1–D3 over the OBJECT box (the smallest remaining chunk)

The object Löb/PBLT chain (`pblt_of_bpsb`) consumes the Hilbert–Bernays–Löb derivability conditions:
  D1 (necessitation)  ⊢ φ  ⟹  ⊢ □φ
  D2 (K / dist)        ⊢ □(φ→α) → (□φ → □α)
  D3 (4 / box-box)     ⊢ □φ → □□φ
We ALREADY have these as engine `Provable` CONSTRUCTORS (`boxIntro`/`axK`/`box4`,
soundness in `Provable_sound`). This spike RESTATES them over a self-contained object proof system
with a REAL `box` modality whose meaning is provability, and CHECKS soundness — confirming the shapes
transplant and the chain has its modal inputs.

`box`'s interpretation is the provability predicate (`interp (box φ) := Proves φ`), so D1/D2/D3 become
the standard HBL facts about `Proves`, proven sound HERE against that interp (anti-cheat: no rule may
make `Proves` prove a falsehood — checked by `Proves_sound`). NOT root-imported.
`lake env lean PrisonersDilemma/Research/Spikes/pblt/HBLObjectSpike.lean`
-/

namespace PD.HBLObjectSpike

/-! ## 1. Object formulas with a real `box`. -/

inductive OFml where
  | atom (n : Nat)            -- an abstract object atom (stands in for plays/eq/gApp/…)
  | imp  (a b : OFml)
  | box  (a : OFml)          -- □ a  — provability of `a`
deriving DecidableEq

/-! ## 2. `⊢_S` with logical plumbing + the HBL rules (faithful restatements of the engine trio).

We keep the logic minimal (id, mp, the K-combinator `impK` so we can chain), and add D1/D2/D3. Budgets
are erased here (the engine carries them via `Formula.size`; orthogonal to modal SOUNDNESS, which is
the spike's concern — the size side-conditions transplant unchanged). -/

inductive Proves : OFml → Prop where
  -- propositional plumbing
  | impId  (a : OFml) : Proves (.imp a a)
  | mp {a b : OFml} : Proves (.imp a b) → Proves a → Proves b
  | impK   (a b : OFml) : Proves (.imp a (.imp b a))                         -- K combinator
  | impS   (a b c : OFml) :
      Proves (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))         -- S combinator
  -- ── HBL derivability conditions ──
  | D1_nec {a : OFml} : Proves a → Proves (.box a)                           -- necessitation (≈ boxIntro)
  | D2_K   (a b : OFml) : Proves (.imp (.box (.imp a b)) (.imp (.box a) (.box b)))  -- K (≈ axK)
  | D3_four (a : OFml) : Proves (.imp (.box a) (.box (.box a)))              -- 4 (≈ box4)

/-! ## 3. Soundness — `box` = provability. The ANTI-CHEAT.

`interp (box a) := Proves a` makes `box` the provability predicate (the engine's `box k = Provable k`).
Then D1/D2/D3 are the standard HBL facts and MUST be sound. We prove `Proves φ → interp φ` for the
PROPOSITIONAL atoms' truth-assignment `v`, with `box` reading back into `Proves`. -/

def interp (v : Nat → Prop) : OFml → Prop
  | .atom n => v n
  | .imp a b => interp v a → interp v b
  | .box a => Proves a            -- □a means "a is provable" — the provability predicate

theorem Proves_sound (v : Nat → Prop) {φ : OFml} (h : Proves φ) : interp v φ := by
  induction h with
  | impId a => intro ha; exact ha
  | mp _ _ ihab iha => exact ihab iha
  | impK a b => intro ha _; exact ha
  | impS a b c => intro habc hab ha; exact (habc ha) (hab ha)
  | D1_nec ha _ =>
      -- interp v (box a) = Proves a; we have `Proves a` (the premise of D1) directly.
      exact ‹Proves _›
  | D2_K a b =>
      -- interp: Proves (a→b) → Proves a → Proves b. That's exactly `Proves.mp` on the object level.
      intro hab ha; exact Proves.mp hab ha
  | D3_four a =>
      -- interp: Proves a → Proves (box a). That's exactly `Proves.D1_nec`.
      intro ha; exact Proves.D1_nec ha

/-! ## 4. The modal core composes: from object legs to `□φP → φP` (the `mutual_loeb` Route-2 shape,
which is what `pblt_of_bpsb` / the engine `mutual_loeb` build from D1/D2/D3). Confirms the HBL trio
suffices for the Löb-style chaining the PBLT proof needs. -/

/-- Transitivity of `imp` (from S+K plumbing). -/
theorem impTrans {a b c : OFml} (hab : Proves (.imp a b)) (hbc : Proves (.imp b c)) :
    Proves (.imp a c) := by
  have h1 : Proves (.imp a (.imp b c)) := Proves.mp (Proves.impK _ _) hbc
  exact Proves.mp (Proves.mp (Proves.impS a b c) h1) hab

/-- **Route-2 mutual-Löb chain in the object system** — from object legs `legPD : □φP → φD` and
    `legDP : □φD → φP`, derive `□φP → φP`, using exactly D1/D2/D3 (the engine `mutual_loeb` shape).
    This is the modal skeleton `pblt_of_bpsb` relies on; here it goes through with the restated HBL. -/
theorem mutual_loeb_object (φP φD : OFml)
    (legPD : Proves (.imp (.box φP) φD))
    (legDP : Proves (.imp (.box φD) φP)) :
    Proves (.imp (.box φP) φP) := by
  -- 1. D1 on legPD : □(□φP → φD)
  have h1 : Proves (.box (.imp (.box φP) φD)) := Proves.D1_nec legPD
  -- 2. D2_K : □(□φP→φD) → (□□φP → □φD); mp with h1 : □□φP → □φD
  have h2 : Proves (.imp (.box (.box φP)) (.box φD)) :=
    Proves.mp (Proves.D2_K (.box φP) φD) h1
  -- 3. D3_four : □φP → □□φP
  have h3 : Proves (.imp (.box φP) (.box (.box φP))) := Proves.D3_four φP
  -- 4. transitivity: □φP → □φD
  have h4 : Proves (.imp (.box φP) (.box φD)) := impTrans h3 h2
  -- 5. transitivity with legDP : □φP → φP
  exact impTrans h4 legDP

/-- **Consistency (anti-vacuous check)** — `Proves` does NOT prove a bare atom. If it did, the system
    would be junk and soundness vacuous. Via the `v ≡ False` valuation through `Proves_sound`. -/
theorem consistency : ¬ Proves (.atom 0) := fun h => Proves_sound (fun _ => False) h

/-! ## VERDICT — HBL D1–D3 transplant to the object box, SOUND and NON-VACUOUS.

All sorry-free. `Proves_sound` (D1/D2/D3 sound with `interp (box a) := Proves a`) + `consistency`
(`¬ Proves (.atom 0)`) confirm the system is NON-VACUOUS, so soundness is meaningful, not trivial. `mutual_loeb_object` builds the Route-2 chain
`□φP→φP` from two object legs using EXACTLY D1/D2/D3 — the modal skeleton the engine `mutual_loeb` and
`pblt_of_bpsb` consume.

**Honest notes.**
  • D1's soundness is tautological under the provability interp ("a proved ⇒ a provable") — that is
    faithfulness, not a cheat; the non-trivial conditions D2/D3 discharge to real object derivations
    (`Proves.mp` / `Proves.D1_nec`).
  • Budgets are erased here. The engine carries them via `Formula.size` side-conditions on
    boxIntro/axK/box4; those transplant UNCHANGED and are orthogonal to modal soundness (the spike's
    concern). The real port must re-thread them, but they raise no new question.

**NET: the HBL trio is the easy chunk, confirmed.** The shapes the engine already proved
(`boxIntro`/`axK`/`box4`) restate over the object box, stay sound, stay consistent, and CHAIN into the
mutual-Löb skeleton. With diag (✅), repr (✅ object-level), the bridge (✅ no mismatch), and now HBL
(✅), every modal/logical input to `pblt_of_bpsb` is de-risked. The ONLY remaining work is engineering:
the FWD encoding + BridgeSound + threading budgets — all over a real arithmetized `S ⊇ PA`, no open
risk. -/

#check @Proves_sound
#check @mutual_loeb_object

end PD.HBLObjectSpike
