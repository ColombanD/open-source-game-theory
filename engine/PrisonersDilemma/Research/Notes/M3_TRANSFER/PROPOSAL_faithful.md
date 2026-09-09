# M3 proposal — angle FAITHFUL (budget-keeping realization, `LenProvableV`, full-Prog evaluator)

Legend: **[V]** = verified in source (file:line cited); **[A]** = my analysis; **[C]** = claim to be turned into Lean (statement given).

## 0. Executive finding (read this first)

**[A, with [V] ingredients] No budget-keeping transfer — same budget (B) or with ANY explicit inflation `e` (B_e), boxes and programs — is true over the full `Pf`.** The refutation is one constructor and one line of Lean:

```lean
-- ProofSystem.lean:162-163  | const : PlaysProof me opponent (.const a) a c_leaf        [V]
-- ProofSystem.lean:273-274  | mk : PlaysProof me opponent me a n → n ≤ k → AtomProvable k (.plays me opponent a)   [V]
example (q : Prog) : Pf 1 (.plays (.const .C) q .C) :=
  Pf.atom (AtomProvable.mk (PlaysProof.const (me := .const .C)) (le_refl _))
```

`AtomProvable` charges EVALUATION STEPS (`n ≤ k`), never the conclusion's size; `Formula.size (.plays p q _) = p.size + q.size + 1` (Program.lean `size`, catalogue §1) is simply not consulted. This is the documented exception `pf_size_or_atom : Pf k φ → φ.size ≤ k ∨ AtomProvable k φ` (T31EngineDecider.lean:176 [V]). Every arithmetical realization of `.plays (.const C) q C` must WRITE `⌜TR q⌝` (the evaluator depends on the opponent's code — `EvalFix.Phi` arm 3 runs `opp`, Eval.lean:33 [V]), so `flen (tr φ) ≥ ‖⌜TR q⌝‖`, unbounded in `q`, while `mlen d ≥ sqlen Γ ≥ flen` of the conclusion for every derivation (`sqlen_le_mlen` Proper.lean:391, `flen_le_sqlen` :343 [V]). Hence for every `e : ℕ → ℕ` there is a `q` with `Pf 1 (.plays (.const .C) q .C)` and `¬ LenProvable fbound (e 1) 𝗣𝗔 ⌜tr (.plays (.const .C) q .C)⌝`. Log-cost numerals (brief §2) do not help: `pBot p = ⟪3,p⟫+1` (Prog.lean:32 [V]) at least squares the code (`Nat.pair 3 p ≥ p²` for `p > 3`), so `‖⌜bot^n (const C)⌝‖ ≥ 2^{n-2}`.

This is not a coding artifact; it is the ONE place where the engine's transcript-cost model departs from Critch's character count (Appendix B: a proof's text contains its conclusion). Two more departures compound it, both [V]:

* `PlaysProof.search_t` cites `Pf k (φ.subst me opp)` at cost `c_guard k = numCost k = log₂ k + 1` (ProofSystem.lean:70-75, :192-195). In PA, certifying "search at budget k succeeded" is `Bew_k(⌜g⌝)`, whose cheapest uniform proof is bounded D1 from the k-proof of g — cost ≥ e*·k (Critch's (d)), not log k. `atom_search_t_top` (Base/AtomCerts.lean:146-152) makes this a budget DROP from `k` to `log₂ k + 3`.
* The `.diag`/box nesting: `Pf K (impl (box n ψ) (box n ψ))` by `implRefl` for `n = 2^{⌊K/2⌋}-1` (literal bound `maxLitF_lt_two_pow_size`, T48:81 [V], is tight) — a formula at budget K legitimately contains boxes at budget ≈ 2^{K/2}. Answering the brief's three questions: (i) premise budgets are strictly below the conclusion in all 10 Pf→Pf glue/modal rules (`pf_pos` T48:673 + `size ≥ 1`), **but NOT in `search_t` / `searchThenSearch_t` / `botSysSearchThenSearch`** (cite at `c_guard`); (ii) YES, box budgets inside φ exceed k exponentially; (iii) T48 bounds `|φ| ≤ k` only off atoms.

Consequently, for the faithful angle, the honest deliverables are: **(T2-NEG)** the machine-checked impossibility above; **(T2-COND)** the exact conditional form of a budget-keeping transfer with every length-tracked obligation as a named hypothesis, and the proof that on the SIZED fragment with those hypotheses the induction goes through; and **(T2-AGENT)** the one budget-keeping statement that is both true and provable at M3: the engine's evaluation certificates are runs of the arithmetized evaluator at the SAME budgets, relative to agreement on the consulted box facts. I recommend the paper state T2 in the budget-erased form (other angles) and cite T2-NEG as the reason.

## 1. Exact Lean statements

All over PA on ℒₒᵣ (actions as numerals 0/1) — the constants `c_C/c_D` and `TAct` exist only for τ-symmetry (RedCell), which T2 does not need; using ℒₒᵣ keeps Foundation's `fixedpoint`/`diagonal` (FixedPoint.lean:126-131 [V], ℒₒᵣ-only) and `sigma_one_completeness` (R0/Basic.lean:143 [V]) directly applicable.

**T2-NEG (theorem, unconditional, M3 deliverable #1).**
```lean
theorem no_budget_keeping_transfer (e : ℕ → ℕ) :
    ∃ (k : ℕ) (φ : PD.Formula), PD.Pf k φ ∧
      ¬ ArithS.LenProvable (fbound : ℕ → ℕ) (e k) 𝗣𝗔 (⌜trB φ⌝ : ℕ)
-- witness k := 1, φ := .plays (.const .C) (botIter (e 1 + 8) (.const .C)) .C
```
Any `trB` with `flen (trB (.plays p q a)) ≥ ‖(⌜TR q⌝ : ℕ)‖` (a hypothesis on the realization, discharged for the concrete `trB` of §2) suffices; state it parametrically so it kills every budget-keeping candidate at once, including ones with log-cost numerals.

**T2-COND (theorem, conditional; the exact form of the "full" budget-keeping T2).**
```lean
/-- The length-tracked derivability facts a budget-keeping transfer needs. Every field is
    a Prop about PA proof LENGTH; none is provable with Foundation's model-theoretic
    completeness (§5). `e` is the box/program inflation, `e₁` the atom certificate cost. -/
structure PALength (e e₁ : ℕ → ℕ) : Prop where
  -- Critch (d): bounded D1 at inflated budgets
  D1 : ∀ kIn K (σ : ArithmeticSentence), kIn + 1 ≤ K →
        𝗣𝗔 ⊢_{e kIn} σ → 𝗣𝗔 ⊢_{e K} □_{e kIn} σ
  -- bounded D2 as a THEOREM of PA (`axKf`) and as a RULE (`axK`, `mp`)
  D2 : ∀ a b c (σ τ : ArithmeticSentence), a + b + 1 ≤ c →
        𝗣𝗔 ⊢_{e c} (□_{e a} (σ ➝ τ) ➝ □_{e b} σ ➝ □_{e c} τ)
  cut : ∀ m₁ m₂ k (σ τ), m₁ + m₂ + 1 ≤ k → 𝗣𝗔 ⊢_{e m₁} (σ ➝ τ) → 𝗣𝗔 ⊢_{e m₂} σ → 𝗣𝗔 ⊢_{e k} τ
  -- bounded D3 (`box4`), internal monotonicity (`boxMono`)
  D3 : ∀ a b (σ), a + 1 ≤ b → 𝗣𝗔 ⊢_{e b} (□_{e a} σ ➝ □_{e b} □_{e a} σ)
  mono : ∀ a b K (σ), a ≤ b → 𝗣𝗔 ⊢_{e K} (□_{e a} σ ➝ □_{e b} σ)
  -- bounded diagonal lemma (`diagF/diagB`), both directions
  diag : ∀ g K (θ : ArithmeticSemisentence 1), 𝗣𝗔 ⊢_{e K} (fixedpoint θ ⭤ θ/[⌜fixedpoint θ⌝])
  -- length-tracked Σ₁-completeness for the evaluator layer (every Family-A arm)
  evalCert : ∀ n me opp body a, PlaysCert n me opp body a →      -- §2.3
        𝗣𝗔 ⊢_{e₁ n} evalSentence me opp body a
  evalRead : ∀ (shape : ReadShape) K, readCost shape ≤ K →      -- searchBranch … searchElseChain
        𝗣𝗔 ⊢_{e K} readSentence shape
  refute : ∀ K (σ : 𝚫₁.Sentence), ¬ ℕ ⊧ σ → 𝗣𝗔 ⊢_{e K} ∼σ  -- atomNeg/eqNeg/search_f suppliers

theorem transfer_bounded (e e₁ : ℕ → ℕ) (h : PALength e e₁)
    {k : ℕ} {φ : PD.Formula} (hs : Sized k φ) (d : PD.Pf k φ) :
    𝗣𝗔 ⊢_{e k} tr_e φ
```
`Sized k φ := φ.size ≤ k` is NOT closed under the rules (unsized atoms enter through `search_t`, §5), so `transfer_bounded` must be stated over the size-gated mirror `PfS` (a `PfG`-style gate, T42PfB.lean:76ff, with `AtomProvable` requiring `n + φ.size ≤ k`). **Verdict:** every field of `PALength` is exactly an M4 item (roadmap §3 M4); `transfer_bounded` has no content the paper can state. I give it because the brief asks for the exact conditional form, not as the deliverable.

**T2-AGENT (theorem, unconditional, M3 deliverable #2).** Budgets kept exactly, no PA proof lengths in the conclusion:
```lean
/-- Engine certificates are runs of the arithmetized evaluator, relative to the consulted
    box facts: at every `.search k ψ` node visited, the engine's `Pf k` verdict and the
    arith oracle `LenProvableV 𝗣𝗔 k ⌜TR(ψ.subst me opp)⌝` agree. -/
theorem playsProof_evalGraph (O : ℕ → PD.Formula → Prop)
    (hO : ∀ k ψ, O k ψ ↔ LenProvableV 𝗣𝗔 (k : ℕ) (⌜trB ψ⌝ : ℕ))
    {me opp body a n} (h : PD.PlaysProof me opp body a n)
    (hag : GuardAgree O h) :                     -- Pf k g ↔ O k g at each search node of h
    ∃ N, EvalGraphP N (TR me) (TR opp) (TR body) (actCode a)
theorem evalGraph_of_playsProof_oracleFree {me opp body a n}
    (h : PD.PlaysProof me opp body a n) (hfree : me.hasSearch = false ∧ opp.hasSearch = false) :
    ∃ N, EvalGraphP N (TR me) (TR opp) (TR body) (actCode a)
theorem evalGraphP_sound (N me opp body a : ℕ) :   -- determinism + the ℕ-truth ⇒ PA-provable, Σ₁
    EvalGraphP N me opp body a → 𝗣𝗔 ⊢ evalSentence N me opp body a
```
`EvalGraphP` is the full-Prog evaluator of §2.3 over `𝗣𝗔` (search clause tests `LenProvableV 𝗣𝗔 k (guardCodeF g me opp)` with `guardCodeF` the internal `tr ∘ subst`). Its meaning: **the agent layer of `S` is PA-sound at the same budgets; the only thing PA-`S` and `S` can disagree on is the oracle** — which is exactly T2-NEG's content restated positively. Corollary worth stating (τ-free, all k): `Pf k (.plays p q a)` with search-free `p q` ⇒ `𝗣𝗔 ⊢ tr (.plays p q a)` (via `atom_complete_searchfree`, AtomCerts.lean:138 [V]).

## 2. The realization `tr` / `TR`

**2.1 Program codes (extend `Prog.lean`).** Keep `pConst pSelf pOpp pBot pSim pIte`; change `pSearch k g p q := ⟪6, k, g, p, q⟫ + 1` where `g` is now a FORMULA CODE (§2.2), not (template, action). Add `pTvote v θ p q := ⟪7, v, θ, p, q⟫+1`, `pSys defs i := ⟪8, defs, i⟫+1`, `pSelfIdx j := ⟪9, j⟫+1`; `VoteList`/`ProgList` as Foundation HFS vectors (`∷`/`0`, `nth`). `TR : Prog → ℕ` structurally, actions `C ↦ 0, D ↦ 1`; budgets KEPT verbatim (`k ↦ k`; in the B_e variant `k ↦ e k` — `e` must then be a `𝚺₁-Function₁` with a definition, e.g. a `PR.Blueprint` iterate, so the internal evaluator can compute it).

**2.2 Formula codes and `TR`-internal twin.** `fPlays p q a := ⟪0,p,q,a⟫+1`, `fImpl`, `fNeg`, `fBox n φ`, `fEq p q`, `fDiag g φ`. `substP/substF` (Program.lean:126-152 [V] semantics: `.bot`, `.tvote` entries, `.sys`, `.eq` RHS, `.diag` FROZEN) as a Δ₁ `Fixpoint` on pairs, exactly the `Relabel` pattern (Prog.lean:197-320 [V]); `sysCloseP/F` likewise (descends into `.eq` both sides and `.diag`, Program.lean:169-197 [V]). Sizes: ~2×300 lines each, mechanical.

**2.3 Meta `tr : Formula → ArithmeticSentence`** (this is what T2-NEG kills as a *bounded* target and T2-AGENT uses):
* `plays p q a ↦ “∃ n, !evalGraphPDef n ⌜TR p⌝ ⌜TR q⌝ ⌜TR p⌝ a”` (Σ₁; `.self/.opp` need no treatment: the evaluator runs `me`/`opp` in frame, Eval.lean arms 2-3).
* `impl ↦ ➝`, `neg ↦ ∼`.
* `box n ψ ↦ (lenProvableV 𝗣𝗔).val/[↑n, ⌜tr ψ⌝]` — the Δ₁ `LenProvableV` (BewV.lean:23-29 [V]) at the numeral `n` (B) or `e n` (B_e).
* `eq p q ↦ “↑(TR p) = ↑(TR q)”`.
* `diag g tgt ↦ fixedpoint “x. !(lenProvableV 𝗣𝗔) ↑g x → !(tr tgt)”` — Foundation's `fixedpoint` (FixedPoint.lean:128 [V]); `diagonal` gives both directions unboundedly. (Alternative used by T2-AGENT only: since `(.diag g φ).interp = Pf g (.diag g φ) → φ.interp` definitionally (Dynamics.lean:158 [V]), a TRUTH-level reading needs no fixed point.)
* **`Formula.subst`**: `tr (ψ.subst me opp)` is computed internally by `trF ∘ substF` — the code equation `⌜tr (ψ.subst me opp)⌝ = trCode (substF ⌜me⌝ ⌜opp⌝ ⌜ψ⌝)` is the M3 analogue of `quote_guardSentence` (Template.lean:235 [V]) and is needed by every search arm; the box case of `trCode` uses `substNumerals` (FixedPoint.lean:29-31 [V]) on the fixed code `⌜(lenProvableV 𝗣𝗔).val⌝`, the diag case needs an internal `diag`-constructor (`qqAll`/`qqImp` over `⌜θ⌝`) — the fiddliest 150 lines.
* **Tau constructors**: `tvote/sys/selfIdx` are COVERED in the evaluator (clauses mirror Dynamics.lean:212-224 [V]: `tvote` peels entries run `.bot`-framed, `sys` closes one level via `sysCloseP`, `selfIdx` has NO clause = `none`); in `Pf` only `botSysSearchStep/botSysSimStep/botSysSearchThenSearch` mention them and they are reading rules over `sysClose`, handled uniformly. No syntactic exclusion is needed; if the evaluator is staged, exclude by `me.hasSearch`-style predicate `noTau`, which IS closed under `subst`/`sysClose` (both preserve constructor tags).

**2.4 Evaluator `EvalGraphP`** = `EvalFix` (Eval.lean:33-74 [V]) + `sim` arm (`⟪n, substP me opp p, substP me opp q, substP me opp p, a⟫ ∈ C`), + `tvote` (three arms), + `sys`, search arm with `LenProvableV 𝗣𝗔 k (trCode (substF me opp g))`. Blueprint stays Δ₁ (`Fixpoint.Blueprint.core : 𝚫₁`, Fixpoint.lean:25-26 [V]) because `lenProvableV` is Δ₁ — this is the reason the bounded box (not `provable`, Σ₁) is the ONLY oracle a Foundation fixpoint can consult; `Finite` (not `StrongFinite`, as now, Eval.lean:162 [V]) since `sim` grows components. Determinism/monotonicity at ℕ as EvalN.lean.

## 3. Per-rule proof plan (every constructor)

Columns: what the arm needs under (B_e, sized fragment) = the field of `PALength`; what T2-AGENT needs (unconditional).

**PlaysProof (15).** `const`: `EvalGraphP.const_iff` (NEW, = EvalN:26 pattern). `self/opp/bot`: `self_iff/opp_iff/bot_iff` (exist for the T1 evaluator, port). `sim`: NEW `sim_iff` + `substP_quote : substP ⌜me⌝ ⌜opp⌝ ⌜p⌝ = ⌜p.subst me opp⌝` (the code equation for `subst`; by `Fixpoint`-induction, ~120 lines). `ite_t/ite_f`: `ite_iff` (exists). `search_t`: `search_iff` + the oracle agreement `hag` (T2-AGENT) / field `D1`+`evalCert` (B_e — and here B_e's induction breaks: the IH is at budget `k` of the guard, the conclusion at `n + log₂ k + 2`; no `PALength` field repairs a budget DROP, so `transfer_bounded` must charge `search_t` at `e₁(n) ≥ e(k)`, i.e. the sized fragment must ALSO re-cost `search_t` to `n + k + c_node`, Critch's (d)). `search_f`: `search_iff` else-branch + `refute` (B_e) / from `Pf m (.neg g)` and PA-soundness `models_of_provable` (Soundness.lean:128 [V]): `¬ LenProvableV k ⌜tr g⌝` is TRUE, which is what `hag` records (T2-AGENT: no field). `voteZero_t/voteNil_f/voteCons_c/voteCons_d/voteHigh_f`: NEW `tvote_*_iff` five inversion lemmas + `VoteAllPlay` motive (`nil`, `cons` : NEW `VoteAllRunP`). `sysStep`: NEW `sys_iff` + `sysCloseP_quote` + `nth_quote` for `ProgList.get?`.

**AtomProvable.mk**: `playsProof_evalGraph` at `body = me` ⇒ `ℕ ⊧ tr (.plays me opp a)` ⇒ `sigma_one_completeness` (R0/Basic.lean:143 [V]) ⇒ `𝗣𝗔 ⊢ tr φ` — UNBOUNDED; bounded needs `evalCert` (field).

**Pf Family A (execution/refutation/reading).** `atom`: as above. `atomNeg`: `EvalGraph.unique'` (EvalN:135 pattern) ⇒ `¬ ℕ ⊧ tr(.plays p q aN)`; `∼tr(plays …)` is Π₁, so provability needs `refute`/… — unbounded route: PA does NOT prove all true Π₁; use instead that `tr(.plays p q aN)` refutation follows from the Σ₁-provable `tr(.plays p q b)` + PA-provable determinism `∀ n n' a a', EvalGraphP n … a → EvalGraphP n' … a' → a = a'` (a uniform IΣ₁ theorem via `complete` from the V-level `unique'` — requires `unique'` for ALL V, currently ℕ-only, EvalN:61-140 [V]: NEW, needs `V`-induction on fuel, `ISigma1.sigma1_order_induction`). Same device for `eqNeg` (`p ≠ q` ⇒ `⌜TR p⌝ ≠ ⌜TR q⌝` by injectivity of `TR` — NEW `TR_injective`; then `𝗣𝗔 ⊢ ↑m ≠ ↑n` is `𝗣𝗔⁻`-provable, `PeanoMinus` numeral lemmas). `eqRefl`: `Entailment` reflexivity. `searchBranch`, `botSearchStep`, `simStep`, `botSimStep`, `iteBranchSearch_t`, `searchChain`, `ctxChain`, `searchElseChain`, `botSysSearchStep`, `botSysSimStep`: all are "PA proves one unfolding of the evaluator at a numeral": `𝗜𝚺₁ ⊢ ∀ …, EvalGraphP (n+1) me opp p a ↔ (arms)` by `complete` from `EvalGraphP.case_iff` (Fixpoint `case`, Fixpoint.lean:222 [V], valid in every `V ⊧* 𝗜𝚺₁`), instantiated with `substP/trCode` code equations; then `cl_prover`. `searchThenSearch_t`, `botSysSearchThenSearch`: same plus the inner `Pf m ψ₂` premise ⇒ (IH, unbounded) `𝗣𝗔 ⊢ tr ψ₂'` ⇒ **needs `LenProvableV k₂ ⌜tr ψ₂'⌝` TRUE = bounded D1** — the arm is dead at the same budget (`m ≤ k₂` cited at `c_guard k₂`); field `D1`. **This is the second hard obstruction: three reading rules consume a box fact at the guard's own budget.**

**Family B (glue).** `mp`, `implTrans`, `weakenImpl`, `impS2`, `implRefl`, `implK`, `implS`, `contrapose`, `negElim`: propositional (`Entailment` `⨀`, `cl_prover`, `C_replace` as in StandardProvability.lean:92-95 [V]); bounded: `cut` field (a hand-built `Derivation2` cut with `mlen` accounting, the ONE field provable at M3, ~200 lines: `Derivation2.cut/wk/and/or` + `mlen` lemma `mlen(cut) = sqlen + m₁ + m₂ + 1`, MetaLength.lean:184 [V]).

**Family C (modal/Löb).** `boxIntro`: needs `LenProvableV kIn ⌜tr φ⌝` TRUE — **bounded D1 = field `D1`; false at same budget (T2-NEG instance: `φ := .plays (.const C) q C`, `kIn := 1`).** `atomBoxImpl`: same (`AtomProvable kBox` ⇒ a PA proof of length ≤ kBox). `axK`: field `D2` + mp. `axKf`: field `D2`. `box4`: field `D3`. `boxMono`: PROVABLE unconditionally: `𝗜𝚺₁ ⊢ ∀ a b φ, a ≤ b → lenProvableV a φ → lenProvableV b φ` by `complete` from `LenProvable.mono`-in-V (Bew.lean:53 [V] is ℕ-level `Monotone f`; `fbound` is `Exp`-monotone in V — NEW 40 lines). `diagF/diagB`: `diagonal` (FixedPoint.lean:130 [V]) gives `𝗣𝗔 ⊢ fixedpoint θ ⭤ θ/[⌜fixedpoint θ⌝]` and `θ/[⌜…⌝]` unfolds to `tr(box g (diag g tgt)) ➝ tr tgt` by `substNumeral_app_quote` (:24 [V]) — UNBOUNDED fine; bounded = field `diag`.

Summary: unconditional PA-provability holds for 9 glue + `boxMono` + `diagF/diagB` + `eqRefl/eqNeg/atomNeg` + `atom` + 12 reading rules; **fails without bounded D1 at `boxIntro`, `atomBoxImpl`, `searchThenSearch_t`, `botSysSearchThenSearch`, `search_t`(budget drop) and without bounded D2/D3 at `axK/axKf/box4`** — 8 arms, all Family C or search-citing, exactly the orchestrator's "equivalent to bounded HBL" conjecture, which I confirm.

## 4. New files / changes (sizes)

* `ArithS/ProgFull.lean` (+700): codes for 10 `Prog` + 6 `Formula` ctors, `substP/substF`, `sysCloseP/F` fixpoints, code equations `substP_quote`, `TR_injective`.
* `ArithS/TrCode.lean` (+400): `trCode` Σ₁ fixpoint incl. box (`substNumerals`) and diag arms; `trCode_quote : trCode ⌜φ⌝ = ⌜tr φ⌝`.
* `ArithS/EvalFull.lean` (+900): `EvalGraphP` with all 10 arms, `Finite`, `case_iff`, inversion; `EvalNFull.lean` (+400): determinism/monotonicity **for all V** (needed by `atomNeg`).
* `ArithS/Transfer/Agent.lean` (+500): T2-AGENT.
* `ArithS/Transfer/Neg.lean` (+250): T2-NEG (`botIter` code lower bound `2^{n-2} ≤ ‖⌜botIter n p⌝‖`, `flen (tr (.plays …)) ≥ ‖⌜TR q⌝‖`, `sqlen_le_mlen`).
* `ArithS/Transfer/Cond.lean` (+600): `PALength`, `PfS` (sized gate), `transfer_bounded`; the `cut` field proved (+200).
* **M1/M2 changes**: log-cost numerals (brief §2 `guard_len_le`) are REQUIRED for the T3 program and for `Dupoc` non-vacuity but NOT by T2-NEG/T2-AGENT (which never bound a length); do them, but as a separate PR (`Length.lean` numeral case in `TermLen.blueprint`, `tlen` twin, `quote_term_le` retower, `fbound` one level taller). `pSearch` re-shaped (§2.1) → `Guard.lean/Template.lean/RedCell.lean` keep the 7-variable template as the special case `g := ⌜Gtmpl⌝`-style via `trCode` of `.plays .opp .self a`; `red_cell` re-proved over the new evaluator (the τ-argument unchanged; ~1 day). Church route: NOT used (`codeOfPartrec'` is opaque, Representation.lean:246 [V]; nothing structural is provable about it).
* Toolchain: T2-AGENT imports `PrisonersDilemma` (needs the v4.33.1 bump, M3_READ_toolchain risks R1-R5); T2-NEG's engine side is one `example`, so it can be developed against the bumped worktree first.

## 5. Risks and fallbacks

1. **T2-COND is contentless** (the failure mode is the whole design): every `PALength` field except `cut`/`mono` requires a length-tracked derivation; Foundation proves `provable_D1`, `provable_D2`, `sigma_one_completeness`, `diagonal` via `complete` (StandardProvability.lean:29-36, R0/Basic.lean:143-148 [V]) — no proof object, no length. Fallback: state `PALength` as the precise M4 obligation, do not put `transfer_bounded` in the paper.
2. **B_e with an explicit `e` is refuted twice more even on the sized fragment [A]**: (a) budget drop at `search_t` (`e(log₂ k+3) ≥ e(k)+c` iterated forces `e(7) = ∞`); (b) coding: `‖⌜σ⌝‖` is ≥ exponential in nesting depth under Cantor pairing and unary numerals (Operator.lean:156-158 [V]), so `tr(box a (box b φ))` is triple-exponentially longer than `|box a (box b φ)|`, while `implRefl (box n ψ)` at budget `K` allows `n ≈ 2^{K/2}` forcing `e(2^{K/2}) ≤ 2^{e K}` — upper and lower growth constraints incompatible with tower-type D1 cost. Fallback: none; this is why the paper's T2 must be budget-erased.
3. **Metatheory debt**: `evalG/decFull` have no tau arms (lakefile header, TAUBOTS.md debt 1 [V]); T2-AGENT does not depend on them.
4. **`atomNeg` needs determinism in every `V`** (currently ℕ-only, EvalN.lean:61 [V]); if `V`-induction fights (`omega` useless on `V`, roadmap traps), fallback: state `atomNeg`'s arm relative to the Σ₁-provable positive atom and the meta fact, i.e. drop `𝗣𝗔 ⊢ ∼…` to `ℕ ⊧ ∼…` (T2-AGENT already lives at ℕ-truth for the else polarity).
5. **Engine change that would make budget-keeping true**: charge `AtomProvable.mk` by `n + φ.size ≤ k` and `search_t` by `n + k + c_node` (Critch (d) with `e* = 1`). This flips `atom_search_t_top`'s `log₂ k + 3` to `k + 3`, breaks the `(2k+64)` staggers and every `universal`-regime cell that relies on cheap citation (`outcome_DupocBot_vs_CooperateBot` pad `atom_cost 1`, vs_CooperateBot.lean:18-21 [V], survives only as `eventual`). Not M3; record as the cost-model finding.

## 6. Paper claim (one paragraph) and its asterisks

> "We arithmetize the agent layer of `S`: programs, their evaluator, and the bounded provability predicate `□_k` (Δ₁ in IΣ₁ by properness) are Foundation objects over PA, and every evaluation certificate of `S` is a run of the arithmetized evaluator at the same budgets, given agreement on the consulted `□_k` facts (T2-AGENT). We prove that this agreement cannot be made unconditional at any budget: `S`'s atom certificates are charged by evaluation steps, not by the size of their conclusion, so `S ⊢₁ (CooperateBot plays C vs q)` for every `q` while no PA proof of the corresponding sentence fits any fixed length (T2-NEG). A budget-keeping soundness theorem `S ⊢_k φ ⇒ PA ⊢_{e(k)} φ*` therefore holds only on a size-gated fragment and only relative to bounded derivability conditions D1–D3 (stated as `PALength`), which are Critch's assumption (d) and are left as the M4 obligation."

Asterisks: (*) T2-AGENT's box agreement is a hypothesis, not a theorem — it IS the missing bounded D1; (**) `PALength` contains no proved field but `cut`/`mono`; (***) the budget-erased T2 (other angles) is the statement without asterisks and should be the headline; (****) all of §4's Foundation lengths depend on Cantor coding — no numeric constant may be quoted (roadmap danger 4).