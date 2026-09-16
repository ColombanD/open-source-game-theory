import ArithS.Necessitation.Verify5
import ArithS.Necessitation.Assemble
import ArithS.Necessitation.Verify4
import ArithS.Necessitation.Bounds
import ArithS.Assembly.Cell
import ArithS.Assembly.Uniform

/-!
# ArithS.Necessitation.Package

**Every theorem here is CONDITIONAL on `SizeThmAll`** (the length/size discipline of the
verification list, `Verify5`'s ten-arm glue, in flight). The names carry `_of_sizeThm` for that
reason: `SizeOracle` (`Assemble` §8) is UNPROVABLE as stated — it binds the numeral table with no
`NumTableOK`, which every prologue size lemma needs and which is never a conclusion — so this file
BYPASSES it. The quantifier order is the repair: `exists_numTable` fixes `N'`/`B'` FIRST, and only
then is the size constant `Cz` chosen, which the layout class `(layQ B B' D, layD N' B' D)` requires. — the package and the headline theorems, with `SizeOracle` BYPASSED

`Assemble.lean` §8 closes at `boundedInnerNec_sixteen_of_size (Cz) (hsz : SizeOracle Cz) : BoundedInnerNec 16`
and `dupoc_self_coop_of_size`, conditional on ONE hypothesis, `Assemble.SizeOracle`.

**`Assemble.SizeOracle` is not provable as stated** (machine-checked, 2026-09-15; the diagnosis is in
`Verify5.lean`'s header): it binds the numeral table `T` universally with NO `NumTableOK T N' B'`, while every
prologue size lemma (`Prologue.sizeOK_layoutSteps`, `sizeOK_proIns`, …) requires one and lands in the class
`(layQ B B' D, layD N' B' D)`, whose only route to the kit class is `Assemble.layQ_le`/`layD_le` — and those need
`N'`, `B'` as NUMBERS. `NumTableOK` is never a conclusion anywhere, so the hypothesis cannot be recovered inside.

This file does not prove `SizeOracle`; it BYPASSES it. The observation is that `SizeOracle`'s ONLY consumer,
`Assemble.kitPackage'''_of_size`, instantiates it at the CANONICAL numeral table of `NumSteps.exists_numTable`,
where `N'` and `B'` are fixed naturals — so a `NumTableOK`-CARRYING size theorem suffices, and `Cz` is allowed to
depend on those two naturals. §1 states that carrying theorem (`SizeThm`, the statement the size glue proves),
§2 re-derives the package from it exactly as `kitPackage'''_of_size` does, and §3 draws the headline theorems.

The results are `Assemble.lean`'s, with the unprovable hypothesis replaced by the provable one.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

/-! ## 1. The carrying size statement -/

section carrying

/-- **The size theorem of the verification list, with the numeral-table hypothesis its proof requires.**

This is `Assemble.VerifySizeOracle` universally quantified over the models and the tables, with
`NumTableOK T (N' : V) (B' : V)` RESTORED — the one hypothesis `Assemble.SizeOracle` drops and every prologue size
lemma needs (`Verify5.verifySizeOracle_of_arms` is the same interface in its per-model form). The constant `Cz` may
therefore depend on the fixed naturals `N'`, `B'`, which is exactly what the layout class `(layQ B B' D, layD N' B' D)`
requires, and is harmless at the use site: the package fixes `N'`, `B'` first (`NumSteps.exists_numTable`) and only
then asks for `Cz`.

Everything else is `VerifySizeOracle`'s shape verbatim: on every `IndRec` table with its row-body bound, every graph
list `L` of a `VerifyGraph''` is `≤ Cz·(dlen ρ + 1)^4` long and size-disciplined at the kit class
`Q = kitQ Cz B E`, `D = kitD Cz (dlen ρ)`. -/
def SizeThm (N N' B' Cv Cz : ℕ) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (tbl B T : V),
    TableOK tbl (N : V) → IndRecTable tbl →
    (∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) →
    formulaLen LAct (Ple : V) ≤ B → NumTableOK T (N' : V) (B' : V) →
    VerifySizeOracle tbl B layoutPieces certPieces frag1Pieces frag2Pieces proPieces T Cv Cz

/-- **The size statement, quantified over the numeral table's naturals** — the shape the size glue delivers
(`Verify5`'s `verifyGraph''_size4 (N' B' : ℕ) : ∃ Cz, …`): for EVERY pair of naturals describing a numeral table
there is a size constant. The quantifier order matters and is the whole point of the bypass: `N'`, `B'` are fixed
first (by `NumSteps.exists_numTable`, inside the package proof), and only then is `Cz` chosen — so `Cz` may depend
on them, which the layout class `(layQ B B' D, layD N' B' D)` requires. -/
def SizeThmAll : Prop := ∀ N N' B' Cv : ℕ, ∃ Cz : ℕ, SizeThm N N' B' Cv Cz

/-- `SizeThm` at a FIXED numeral table gives precisely `Assemble.VerifySizeOracle` — the shape
`Assemble.verifyKit'''_of` consumes. (The content of the bypass: the missing hypothesis is available at the use
site, because the use site owns the table.) -/
theorem verifySizeOracle_of_sizeThm {N N' B' Cv Cz : ℕ} (hsz : SizeThm N N' B' Cv Cz)
    {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl B T : V}
    (htbl : TableOK tbl (N : V))
    (hPA : IndRecTable tbl) (hB : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (htblN : NumTableOK T (N' : V) (B' : V)) :
    VerifySizeOracle tbl B layoutPieces certPieces frag1Pieces frag2Pieces proPieces T Cv Cz :=
  hsz V tbl B T htbl hPA hB hPle htblN

end carrying

/-! ## 2. The package at `m = 4`, from the carrying size theorem -/

section package

/-- **The package holds at `m = 4`, from the CARRYING size theorem** — `Assemble.kitPackage'''_of_size` with
`SizeOracle` replaced by `SizeThm`.

The proof is `kitPackage'''_of_size`'s, in the one order that makes the bypass work: `exists_numTable` FIRST (it
fixes `N'`, `B'` as naturals), then the size theorem AT those naturals, then `verifyKit'''_of N' B' Cz C` — so the
size constant is applied at the canonical numeral table `tblN`, where `NumTableOK tblN N' B'` is in hand. -/
theorem kitPackage'''_of_size' (hsz : SizeThmAll) :
    ∃ (N B N' B' N₂ B₂ N₃ B₃ Ck Cv : ℕ) (Cχ : Semisentence LAct 1 → ℕ),
      KitPackage''' N B N' B' N₂ B₂ N₃ B₃ Ck Cv Cχ 4 := by
  obtain ⟨N, B₀, hTab⟩ := exists_indRecTableB
  obtain ⟨N', B', hNum⟩ := exists_numTable
  obtain ⟨N₂, B₂, hLen⟩ := exists_lenTable
  obtain ⟨N₃, B₃, hMul⟩ := exists_mulTable
  obtain ⟨C, hex⟩ := verifyGraph''_exists_unconditional
  obtain ⟨Cz, hCz⟩ := hsz N N' B' C
  obtain ⟨Ck, hkit⟩ := verifyKit'''_of N' B' Cz C
  refine ⟨N, B₀ + cPlength + cPeq + cPle, N', B', N₂, B₂, N₃, B₃, Ck, C,
    fun χ ↦ Classical.choose (pinKit'_of χ N' B'), fun V _ _ ↦ ?_⟩
  obtain ⟨tbl, htbl, hPA, hB₀⟩ := hTab V
  obtain ⟨tblN, hN⟩ := hNum V
  obtain ⟨tblL, hL⟩ := hLen V
  obtain ⟨tblM, hM⟩ := hMul V
  have hB : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ ((B₀ + cPlength + cPeq + cPle : ℕ) : V) := fun j hj ↦
    le_trans (hB₀ j hj) (by exact_mod_cast (by omega : B₀ ≤ B₀ + cPlength + cPeq + cPle))
  have hPl : formulaLen LAct (Plength : V) ≤ ((B₀ + cPlength + cPeq + cPle : ℕ) : V) := by
    rw [formulaLen_Plength_eq]; exact_mod_cast (by omega : cPlength ≤ B₀ + cPlength + cPeq + cPle)
  have hPeq : formulaLen LAct (Peq : V) ≤ ((B₀ + cPlength + cPeq + cPle : ℕ) : V) := by
    rw [formulaLen_Peq_eq]; exact_mod_cast (by omega : cPeq ≤ B₀ + cPlength + cPeq + cPle)
  have hPle : formulaLen LAct (Ple : V) ≤ ((B₀ + cPlength + cPeq + cPle : ℕ) : V) := by
    rw [formulaLen_Ple_eq]; exact_mod_cast (by omega : cPle ≤ B₀ + cPlength + cPeq + cPle)
  refine ⟨tbl, layoutPieces, certPieces, frag1Pieces, frag2Pieces, proPieces, tblN, tblL, tblM, htbl,
    hPA.proTable.topTable, hB, hPl, hPeq, hPle, hN, hL, hM, ?_, ?_, ?_⟩
  · intro ρ E hd hE
    exact hex V htbl hPA rfl rfl rfl hd hE
  · exact hkit V htbl hPA.proTable hB hPle hN rfl rfl rfl rfl rfl
      (verifySizeOracle_of_sizeThm hCz htbl hPA hB hPle hN)
  · intro χ
    exact Classical.choose_spec (pinKit'_of χ N' B') V htbl hPA.numIdTable hB hN

end package

/-! ## 2.5 THE CARRYING SIZE THEOREM, DISCHARGED

`Verify5.armHypsAll_of_arms` chooses the size constant for each `(N, N', B', Cv)`, and
`Verify5.verifyGraph''_size4_of_arms` turns `ArmHypsAll` into `SizeThm`'s shape verbatim —
the two statements are now the same binder list and the same `VerifySizeOracle` target. So
`SizeThmAll` holds outright, and every theorem below that took it as a hypothesis is
unconditional. -/

theorem sizeThmAll_holds : SizeThmAll := by
  intro N N' B' Cv
  obtain ⟨Cz, harms⟩ := armHypsAll_of_arms N N' B' Cv
  exact ⟨Cz, verifyGraph''_size4_of_arms N N' B' harms⟩

/-! ## 3. The headline theorems, UNCONDITIONAL modulo the carrying size theorem -/

section headline

/-- **`BoundedInnerNec 16`** (`deg 4 = 16`) from the carrying size theorem — `Assemble`'s
`boundedInnerNec_sixteen_of_size` with the unprovable `SizeOracle` replaced. -/
theorem boundedInnerNec_sixteen_of_sizeThm (hsz : SizeThmAll) : BoundedInnerNec 16 := by
  obtain ⟨N, B, N', B', N₂, B₂, N₃, B₃, Ck, Cv, Cχ, hpkg⟩ := kitPackage'''_of_size' hsz
  exact boundedInnerNec_of_kit''' 4 (by norm_num) hpkg

/-- **Critch's Theorem 3.7 in PA-`S`**: for all large `k`, `Dupoc k` cooperates with itself and `Cupod k` defects
against itself (`Assembly/Cell.dupoc_self_coop` at `d = 16`). -/
theorem dupoc_self_coop_of_sizeThm (hsz : SizeThmAll) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Dupoc k) (Dupoc k) (Dupoc k) 0 ∧ EvalGraph 2 (Cupod k) (Cupod k) (Cupod k) 1 :=
  dupoc_self_coop (boundedInnerNec_sixteen_of_sizeThm hsz)

/-- **The parametric bounded Löb theorem (PBLT) in PA-`S`**, uniform in the budget
(`Assembly/Uniform.pblt_uniform` at `d = 16`). -/
theorem pblt_of_sizeThm (hsz : SizeThmAll) :
    ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psi) :=
  pblt_uniform (boundedInnerNec_sixteen_of_sizeThm hsz)

end headline

end ArithS
