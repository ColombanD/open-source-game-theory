import PrisonersDilemma.Base.AtomCerts

/-!
# Base/ValuationSoundness — the parametric valuation-soundness MASTER LEMMA

ONE budget-strong induction + raw mutual recursion (`wv_sound_upto`) that yields, at
every instantiation of its interface:

* **plain soundness** (`S = S' = ∅`): `sound_upto` in `Base/Soundness` — every
  bounded proof is true, every certificate is a real play;
* **modified-valuation soundness** (the WaryBot censuses, `Theorems/WaryBot/Helpers`):
  `Pf K φ → WV S φ` for a valuation `WV S` that makes the fixpoint-entangled C-atoms
  `S` unconditionally true — the engine behind the `.neg`-guard Löb-fixpoint outcome
  theorems (`¬ Pf K (.neg (.plays MirrorBot (WaryBot k) .C))` at EVERY budget, and
  the self-play twin).

**Why ONE lemma with paired motives.** The two results need OPPOSITE induction
disciplines and each fails alone:
* soundness needs the budget-strong induction — `search_f`'s arm must refute a
  HYPOTHETICAL guard proof `Pf k guard` that is not a sub-derivation; the `search_f`
  cost floor puts `k` strictly below the certificate's own cost, so the outer IH at
  `k < B` supplies its truth;
* the censuses need the STRUCTURAL cross-IH through `search_t`'s guard back-edge —
  the guard proof sits at the searcher's OWN literal budget `k`, of which the node's
  transcript contains only `numCost k`, so no budget measure descends; only the
  (finite) proof TREE does.
The master carries both: each `Pf` motive is a pair — a budget-GATED soundness half
(`k ≤ B → interp`) and an UNGATED census half. The census half is conditional on
full soundness (`(∀ K χ, Pf K χ → χ.interp) → WV S φ`), because its transparency-leaf
arms need `interp` of rebuilt constructors at budgets the gate cannot reach (nodes
UNDER a guard back-edge can exceed `B`); the condition is discharged AFTER extraction
(first extract `sound_upto`/`Pf_sound` from the gated halves at `S = ∅`, then feed it
back). No circularity: `Pf_sound` never consumes a census half.

**The interface** (`S` = the WV-affecting atom pairs; `S'` = auxiliary play-C-forced
pairs that do NOT enter the valuation — e.g. the mirror census's `(WaryBot k,
MirrorBot)` companion pair): per-shape kill/closure obligations on `T := S ∪ S'`,
exactly what the execution-side arms consume. Empty relations discharge everything
vacuously.

**PROJECT-CONVENTION NOTE (raw mutual recursor).** The codebase rule is "never use
the raw mutual recursors outside ProofSystem.lean §4 and the soundness spine". This
file IS the soundness spine's induction — the third and intended FINAL raw-recursor
site (with `ProofSystem.lean` §4). It exists precisely so that no future valuation
argument ever re-runs the 39-arm induction: INSTANTIATE `wv_sound_upto`, never
re-induct. (History: `sound_upto` and the two WaryBot census inductions were three
separate raw-recursor proofs before 2026-07-30; this lemma is their merge.)
-/

open Classical

open PD
namespace PD.BaseTheorems

/-! ## Fuel monotonicity and the telescope-soundness cores

(Moved here from `Base/Soundness` 2026-07-30 — the master lemma's arms need them;
same namespace, so downstream references are unaffected.) -/

/-- Fuel monotonicity of `eval`: a successful run survives more fuel. Standard;
    by strong induction on the fuel, generalized over all of `me`/`opp`/`body`
    (the `.sim` case swaps players). -/
theorem eval_mono :
    ∀ (N : Nat) (me opponent body : Prog) (a : Action),
      eval N me opponent body = some a → eval (N+1) me opponent body = some a := by
  intro N
  induction N with
  | zero => intro me opponent body a h; simp [eval] at h
  | succ n ih =>
    intro me opponent body a h
    cases body with
    | const c => simpa [eval] using h
    | self => rw [eval] at h ⊢; exact ih _ _ _ _ h
    | opp => rw [eval] at h ⊢; exact ih _ _ _ _ h
    | bot p => rw [eval] at h ⊢; exact ih _ _ _ _ h
    | sim p q => rw [eval] at h ⊢; exact ih _ _ _ _ h
    | ite b a' p q =>
        rw [eval] at h ⊢
        cases hb : eval n me opponent b with
        | none => simp [hb] at h
        | some r =>
            rw [hb] at h; rw [ih me opponent b r hb]
            simp only [bind, Option.bind] at h ⊢
            by_cases hr : (r == a') = true
            · rw [if_pos hr] at h ⊢; exact ih _ _ _ _ h
            · rw [if_neg hr] at h ⊢; exact ih _ _ _ _ h
    | search k φ p q =>
        rw [eval] at h ⊢
        by_cases hg : proofSearch k (φ.subst me opponent) = true
        · rw [if_pos hg] at h ⊢; exact ih _ _ _ _ h
        · rw [if_neg hg] at h ⊢; exact ih _ _ _ _ h

/-- `≤`-form of fuel monotonicity. -/
theorem eval_mono_le {me opponent body : Prog} {a : Action} {N : Nat}
    (h : eval N me opponent body = some a) : ∀ M, N ≤ M → eval M me opponent body = some a := by
  intro M hM
  induction hM with
  | refl => exact h
  | step _ ih => exact eval_mono _ _ _ _ _ ih

theorem implChain_interp {tgt : Formula} : ∀ (gs : List Formula),
    ((∀ ψ ∈ gs, ψ.interp) → tgt.interp) → (implChain gs tgt).interp := by
  intro gs
  induction gs with
  | nil =>
      intro h
      exact h (fun ψ hψ => nomatch hψ)
  | cons g gs ih =>
      intro h hgI
      refine ih (fun hall => h ?_)
      intro ψ hψ
      rcases List.mem_cons.mp hψ with h1 | h2
      · exact h1 ▸ hgI
      · exact hall ψ h2

theorem searchPlug_eval (me opponent : Prog) (a : Action) :
    ∀ (L : List (Nat × Formula × Prog)),
      (∀ ψ ∈ searchGuards me opponent L, ψ.interp) →
      ∃ n, eval n me opponent (searchPlug L (.const a)) = some a := by
  intro L
  induction L with
  | nil => exact fun _ => ⟨1, rfl⟩
  | cons hd rest ih =>
      obtain ⟨g, ψ, e⟩ := hd
      intro hg
      have hhead : Pf g (ψ.subst me opponent) := hg _ List.mem_cons_self
      have hps : proofSearch g (ψ.subst me opponent) = true :=
        (proofSearch_spec _ _).2 hhead
      obtain ⟨n, hn⟩ := ih (fun ψ' h' => hg ψ' (List.mem_cons_of_mem _ h'))
      refine ⟨n + 1, ?_⟩
      show eval (n + 1) me opponent (.search g ψ (searchPlug rest (.const a)) e) = some a
      rw [eval, if_pos hps]
      exact hn

/-- The MIXED-telescope eval induction (the ite frontier, 2026-07-28): if every guard
    fact of a `CtxLayer` stack holds — provable boxes for search layers, real probe
    plays for ite layers — evaluation reaches the plugged constant. -/
theorem ctxPlug_eval (me opponent : Prog) (a : Action) :
    ∀ (L : List CtxLayer),
      (∀ ψ ∈ ctxGuards me opponent L, ψ.interp) →
      ∃ n, eval n me opponent (ctxPlug L (.const a)) = some a := by
  intro L
  induction L with
  | nil => exact fun _ => ⟨1, rfl⟩
  | cons hd rest ih =>
      cases hd with
      | searchL g ψ e =>
          intro hg
          have hhead : Pf g (ψ.subst me opponent) := hg _ List.mem_cons_self
          have hps : proofSearch g (ψ.subst me opponent) = true :=
            (proofSearch_spec _ _).2 hhead
          obtain ⟨n, hn⟩ := ih (fun ψ' h' => hg ψ' (List.mem_cons_of_mem _ h'))
          refine ⟨n + 1, ?_⟩
          show eval (n + 1) me opponent (.search g ψ (ctxPlug rest (.const a)) e) = some a
          rw [eval, if_pos hps]
          exact hn
      | iteL z aT other =>
          intro hg
          have hprobe : (Formula.plays opponent (.bot z) aT).interp :=
            hg _ List.mem_cons_self
          obtain ⟨nb, hb⟩ := hprobe
          -- `nb ≥ 1`: a fuel-`0` play is `none ≠ some aT`.
          obtain ⟨m, rfl⟩ : ∃ m, nb = m + 1 := by
            cases nb with
            | zero => simp [play, eval] at hb
            | succ m => exact ⟨m, rfl⟩
          have hguard : eval (m + 1) opponent (.bot z) opponent = some aT := hb
          obtain ⟨n, hn⟩ := ih (fun ψ' h' => hg ψ' (List.mem_cons_of_mem _ h'))
          have hguardN : eval (max (m + 1) n + 1) me opponent (.sim .opp (.bot z))
              = some aT := by
            rw [show eval (max (m + 1) n + 1) me opponent (.sim .opp (.bot z))
                  = eval (max (m + 1) n) opponent (.bot z) opponent from rfl]
            exact eval_mono_le hguard _ (Nat.le_max_left _ _)
          have hbeq : (aT == aT) = true := by cases aT <;> rfl
          refine ⟨max (m + 1) n + 1 + 1, ?_⟩
          show eval _ me opponent
            (.ite (.sim .opp (.bot z)) aT (ctxPlug rest (.const a)) other) = some a
          rw [eval, hguardN]
          simp only [bind, Option.bind]
          rw [if_pos hbeq]
          exact eval_mono_le hn _ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _))

/-! ## The modified valuation `WV`, parametric over the entangled-atom relation

`WV S` is `Formula.interp` with ONE change: a plays-atom is additionally true when
its action is `.C` and its player pair is in `S`. Boxes stay RAW `Pf` — that is what
keeps the modal tier and the transparency leaves sound without touching the Löb
machinery. `WV (fun _ _ => False)` is pointwise equivalent to `interp` (not needed
below — the master exposes the `interp` half directly). -/

def WV (S : Prog → Prog → Prop) : Formula → Prop
  | .plays p q a => (a = .C ∧ S p q) ∨ (Formula.plays p q a).interp
  | .impl α β => WV S α → WV S β
  | .neg φ => ¬ WV S φ
  | .box n φ => Pf n φ
  | .eq p q => p = q
  | .diag g φ => Pf g (.diag g φ) → WV S φ

theorem WV_plays {S : Prog → Prog → Prop} {p q : Prog} {a : Action} :
    WV S (.plays p q a) = ((a = .C ∧ S p q) ∨ (Formula.plays p q a).interp) := rfl
theorem WV_impl {S : Prog → Prog → Prop} {α β : Formula} :
    WV S (.impl α β) = (WV S α → WV S β) := rfl
theorem WV_neg {S : Prog → Prog → Prop} {φ : Formula} :
    WV S (.neg φ) = ¬ WV S φ := rfl
theorem WV_box {S : Prog → Prog → Prop} {n : Nat} {φ : Formula} :
    WV S (.box n φ) = Pf n φ := rfl
theorem WV_eq {S : Prog → Prog → Prop} {p q : Prog} :
    WV S (.eq p q) = (p = q) := rfl
theorem WV_diag {S : Prog → Prog → Prop} {g : Nat} {φ : Formula} :
    WV S (.diag g φ) = (Pf g (.diag g φ) → WV S φ) := rfl

/-- Probe atoms (`.bot`-frozen opponent) fall out of any `S` that avoids `.bot`
    opponents, so their WV is their interp. -/
theorem interp_of_WV_probe {S : Prog → Prog → Prop}
    (hnb : ∀ oppo z, ¬ S oppo (.bot z)) {oppo z : Prog} {aT : Action}
    (h : WV S (.plays oppo (.bot z) aT)) :
    (Formula.plays oppo (.bot z) aT).interp := by
  rw [WV_plays] at h
  rcases h with ⟨-, hSP⟩ | h
  · exact absurd hSP (hnb oppo z)
  · exact h

/-- Interp-to-WV bridge along a search-guard chain (box antecedents: WV = interp;
    the plays tail embeds by `Or.inr`). -/
theorem WV_of_interp_searchChain {S : Prog → Prog → Prop} (me oppo : Prog)
    (a : Action) :
    ∀ L : List (Nat × Formula × Prog),
      (implChain (searchGuards me oppo L) (.plays me oppo a)).interp →
      WV S (implChain (searchGuards me oppo L) (.plays me oppo a))
  | [] => fun h => Or.inr h
  | (g, ψ, e) :: L => by
      intro h
      show WV S (.impl (.box g (ψ.subst me oppo))
        (implChain (searchGuards me oppo L) (.plays me oppo a)))
      rw [WV_impl]
      intro hbox
      rw [WV_box] at hbox
      exact WV_of_interp_searchChain me oppo a L (h hbox)

/-- Interp-to-WV bridge along a mixed-telescope guard chain. -/
theorem WV_of_interp_ctxChain {S : Prog → Prog → Prop}
    (hnb : ∀ oppo z, ¬ S oppo (.bot z)) (me oppo : Prog) (a : Action) :
    ∀ L : List CtxLayer,
      (implChain (ctxGuards me oppo L) (.plays me oppo a)).interp →
      WV S (implChain (ctxGuards me oppo L) (.plays me oppo a))
  | [] => fun h => Or.inr h
  | .searchL g ψ e :: L => by
      intro h
      show WV S (.impl (.box g (ψ.subst me oppo))
        (implChain (ctxGuards me oppo L) (.plays me oppo a)))
      rw [WV_impl]
      intro hbox
      rw [WV_box] at hbox
      exact WV_of_interp_ctxChain hnb me oppo a L (h hbox)
  | .iteL z aT other :: L => by
      intro h
      show WV S (.impl (.plays oppo (.bot z) aT)
        (implChain (ctxGuards me oppo L) (.plays me oppo a)))
      rw [WV_impl]
      intro hprobe
      exact WV_of_interp_ctxChain hnb me oppo a L (h (interp_of_WV_probe hnb hprobe))

/-! ## THE MASTER LEMMA -/

set_option maxHeartbeats 1600000 in
/-- **The parametric valuation-soundness master lemma.** See the file header for the
    architecture (paired motives: budget-gated soundness ∧ soundness-conditional
    census). Instantiations: `sound_upto` (`S = S' = ∅`, Base/Soundness) and the two
    WaryBot censuses (`Theorems/WaryBot/Helpers`). INSTANTIATE — never re-induct. -/
theorem wv_sound_upto (S S' : Prog → Prog → Prop)
    (h_nb : ∀ oppo z, ¬ S oppo (.bot z))
    (h_const : ∀ me oppo a, (S me oppo ∨ S' me oppo) →
      (Prog.const a = me ∨ me = .bot (.const a)) → a = .C)
    (h_opp : ∀ me oppo, (S me oppo ∨ S' me oppo) →
      (Prog.opp = me ∨ me = .bot .opp) → False)
    (h_ite : ∀ me oppo b a' p q, (S me oppo ∨ S' me oppo) →
      (Prog.ite b a' p q = me ∨ me = .bot (.ite b a' p q)) → False)
    (h_botbot : ∀ me oppo p, (S me oppo ∨ S' me oppo) → me = .bot (.bot p) → False)
    (h_botsearch : ∀ me oppo g ψ P Q, (S me oppo ∨ S' me oppo) →
      me = .bot (.search g ψ P Q) → False)
    (h_sim_inv : ∀ p q oppo, (S (.sim p q) oppo ∨ S' (.sim p q) oppo) →
      S (p.subst (.sim p q) oppo) (q.subst (.sim p q) oppo) ∨
      S' (p.subst (.sim p q) oppo) (q.subst (.sim p q) oppo))
    (h_botsim_inv : ∀ p q oppo,
      (S (.bot (.sim p q)) oppo ∨ S' (.bot (.sim p q)) oppo) →
      S (p.subst (.bot (.sim p q)) oppo) (q.subst (.bot (.sim p q)) oppo) ∨
      S' (p.subst (.bot (.sim p q)) oppo) (q.subst (.bot (.sim p q)) oppo))
    (h_search_t : ∀ oppo g ψ P Q a n,
      (S (.search g ψ P Q) oppo ∨ S' (.search g ψ P Q) oppo) →
      WV S (ψ.subst (.search g ψ P Q) oppo) →
      PlaysProof (.search g ψ P Q) oppo P a n → a = .C)
    (h_search_f : ∀ oppo g ψ P Q a n,
      (S (.search g ψ P Q) oppo ∨ S' (.search g ψ P Q) oppo) →
      PlaysProof (.search g ψ P Q) oppo Q a n → a = .C)
    (h_simS : ∀ p q oppo, S (p.subst (.sim p q) oppo) (q.subst (.sim p q) oppo) →
      S (.sim p q) oppo)
    (h_botsimS : ∀ p q oppo,
      S (p.subst (.bot (.sim p q)) oppo) (q.subst (.bot (.sim p q)) oppo) →
      S (.bot (.sim p q)) oppo) :
    ∀ B : Nat,
    (∀ me opponent body a n, PlaysProof me opponent body a n → n ≤ B →
      ∃ N, eval N me opponent body = some a)
    ∧ (∀ k φ, Pf k φ →
        (k ≤ B → φ.interp) ∧ ((∀ K χ, Pf K χ → χ.interp) → WV S φ)) := by
  intro B
  induction B using Nat.strong_induction_on with
  | _ B IH =>
    -- ── PASS 1: the certificate half (gated eval-soundness; Pf motives `True`) ──
    have hplays : ∀ me opponent body a n, PlaysProof me opponent body a n → n ≤ B →
        ∃ N, eval N me opponent body = some a := by
      intro me opponent body a n h
      refine PlaysProof.rec
        (motive_1 := fun me opponent body a n _ =>
          n ≤ B → ∃ N, eval N me opponent body = some a)
        (motive_2 := fun _ _ _ => True)
        (motive_3 := fun _ _ _ => True)
        ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?search_f ?atomMk
        ?pfAtom ?pfAtomNeg ?pfSearchBranch ?pfSimStep ?pfBotSimStep ?pfBotSearchStep
        ?pfIteBranchSearch ?pfSTS ?pfSearchChain ?pfCtxChain ?pfEqRefl ?pfEqNeg ?pfMp
        ?pfImplTrans
        ?pfWeaken ?pfImpS2 ?pfImplRefl ?pfImplK ?pfImplS ?pfContrapose ?pfNegElim
        ?pfBoxIntro ?pfAtomBoxImpl ?pfAxK ?pfAxKf ?pfBox4 ?pfBoxMono ?pfDiagF ?pfDiagB h
      case const => exact fun _ => ⟨1, rfl⟩
      case self =>
        intro me opponent a n _ ih hB
        obtain ⟨N, hN⟩ := ih (by omega)
        exact ⟨N+1, by rw [eval]; exact hN⟩
      case opp =>
        intro me opponent a n _ ih hB
        obtain ⟨N, hN⟩ := ih (by omega)
        exact ⟨N+1, by rw [eval]; exact hN⟩
      case bot =>
        intro me opponent p a n _ ih hB
        obtain ⟨N, hN⟩ := ih (by omega)
        exact ⟨N+1, by rw [eval]; exact hN⟩
      case sim =>
        intro a n me opponent p q _ ih hB
        obtain ⟨N, hN⟩ := ih (by omega)
        exact ⟨N+1, by rw [eval]; exact hN⟩
      case ite_t =>
        intro me opponent b r m a' p a n q _ hr _ ihb ihp hB
        obtain ⟨Nb, hNb⟩ := ihb (by omega)
        obtain ⟨Np, hNp⟩ := ihp (by omega)
        refine ⟨max Nb Np + 1, ?_⟩
        rw [eval, eval_mono_le hNb _ (Nat.le_max_left Nb Np)]
        simp only [bind, Option.bind]; rw [if_pos hr]
        exact eval_mono_le hNp _ (Nat.le_max_right Nb Np)
      case ite_f =>
        intro me opponent b r m a' q a n p _ hr _ ihb ihq hB
        obtain ⟨Nb, hNb⟩ := ihb (by omega)
        obtain ⟨Nq, hNq⟩ := ihq (by omega)
        refine ⟨max Nb Nq + 1, ?_⟩
        rw [eval, eval_mono_le hNb _ (Nat.le_max_left Nb Nq)]
        simp only [bind, Option.bind]; rw [if_neg (by simp [hr])]
        exact eval_mono_le hNq _ (Nat.le_max_right Nb Nq)
      case search_t =>
        intro k me opponent p a n φ q hguard _ _ ihp hB
        obtain ⟨Np, hNp⟩ := ihp (by omega)
        exact ⟨Np+1, by
          rw [eval, if_pos ((proofSearch_spec k (φ.subst me opponent)).2 hguard)]
          exact hNp⟩
      case search_f =>
        intro m me opponent q a n k φ p hneg _ _ ihq hB
        have hcn : c_node = 1 := rfl
        -- the refutation's interp, via the strong IH strictly below B
        have hnegI : ¬ (φ.subst me opponent).interp :=
          (((IH m (by omega)).2 m (.neg (φ.subst me opponent)) hneg).1 le_rfl : _)
        -- the guard is unprovable at its own budget k (< the certificate's cost — the FLOOR)
        have hps : proofSearch k (φ.subst me opponent) = false := by
          cases hcase : proofSearch k (φ.subst me opponent) with
          | false => rfl
          | true =>
              exact absurd
                (((IH k (by omega)).2 k _ ((proofSearch_spec _ _).1 hcase)).1 le_rfl) hnegI
        obtain ⟨N, hN⟩ := ihq (by omega)
        exact ⟨N+1, by rw [eval, if_neg (by simp [hps])]; exact hN⟩
      all_goals (intros; trivial)
    -- ── PASS 2: the `Pf` half (paired motives: gated interp ∧ conditional WV) ──
    have hpf : ∀ k φ, Pf k φ →
        (k ≤ B → φ.interp) ∧ ((∀ K χ, Pf K χ → χ.interp) → WV S φ) := by
      intro k φ h
      refine Pf.rec
        (motive_1 := fun me oppo body a n _ =>
          (∀ K χ, Pf K χ → χ.interp) → (S me oppo ∨ S' me oppo) →
          (body = me ∨ me = .bot body) → a = .C)
        (motive_2 := fun m ψ _ =>
          (m ≤ B → ψ.interp) ∧
          ((∀ K χ, Pf K χ → χ.interp) → ∀ p q, S p q → ψ ≠ .plays p q .D))
        (motive_3 := fun k ψ _ =>
          (k ≤ B → ψ.interp) ∧ ((∀ K χ, Pf K χ → χ.interp) → WV S ψ))
        ?cConst ?cSelf ?cOpp ?cBot ?cSim ?cIte_t ?cIte_f ?cSearch_t ?cSearch_f ?cAtomMk
        ?pAtom ?pAtomNeg ?pSearchBranch ?pSimStep ?pBotSimStep ?pBotSearchStep
        ?pIteBranchSearch ?pSTS ?pSearchChain ?pCtxChain ?pEqRefl ?pEqNeg ?pMp ?pImplTrans
        ?pWeaken ?pImpS2 ?pImplRefl ?pImplK ?pImplS ?pContrapose ?pNegElim
        ?pBoxIntro ?pAtomBoxImpl ?pAxK ?pAxKf ?pBox4 ?pBoxMono ?pDiagF ?pDiagB h
      -- ── the certificate side: the census play-exclusion clause ──
      case cConst =>
        intro me oppo a _hs hT hgate
        exact h_const me oppo a hT hgate
      case cSelf =>
        -- generic: the premise's body IS `me`, so its own gate closes reflexively
        intro me oppo a n _hpl ih hs hT _hgate
        exact ih hs hT (Or.inl rfl)
      case cOpp =>
        intro me oppo a n _hpl _ih _hs hT hgate
        exact (h_opp me oppo hT hgate).elim
      case cBot =>
        intro me oppo p a n _hpl ih hs hT hgate
        rcases hgate with hb | hb
        · exact ih hs hT (Or.inr hb.symm)
        · exact (h_botbot me oppo p hT hb).elim
      case cSim =>
        intro a n me oppo p q _hpl ih hs hT hgate
        rcases hgate with hb | hb
        · subst hb
          exact ih hs (h_sim_inv p q oppo hT) (Or.inl rfl)
        · subst hb
          exact ih hs (h_botsim_inv p q oppo hT) (Or.inl rfl)
      case cIte_t =>
        intro me oppo b r m a' p a n q _hb _hr _hp _ihb _ihp _hs hT hgate
        exact (h_ite me oppo b a' p q hT hgate).elim
      case cIte_f =>
        intro me oppo b r m a' q a n p _hb _hr _hq _ihb _ihq _hs hT hgate
        exact (h_ite me oppo b a' p q hT hgate).elim
      case cSearch_t =>
        intro K' me oppo p a n φg q hg hp ihg _ihp hs hT hgate
        rcases hgate with hb | hb
        · subst hb
          exact h_search_t oppo K' φg p q a n hT (ihg.2 hs) hp
        · exact (h_botsearch me oppo K' φg p q hT hb).elim
      case cSearch_f =>
        intro m me oppo q a n K' φg p _hg hq _ihg _ihq hs hT hgate
        rcases hgate with hb | hb
        · subst hb
          exact h_search_f oppo K' φg p q a n hT hq
        · exact (h_botsearch me oppo K' φg p q hT hb).elim
      case cAtomMk =>
        intro me oppo a n K hpp hn ih
        constructor
        · intro hB
          exact hplays me oppo me a n hpp (by omega)
        · intro hs p q hSP heq
          injection heq with h1 h2 h3
          subst h1; subst h2; subst h3
          exact Action.noConfusion (ih hs (Or.inl hSP) (Or.inl rfl))
      -- ── the `Pf` side: ⟨gated soundness, conditional WV⟩ per arm ──
      case pAtom =>
        intro k0 φ0 hatom ih
        constructor
        · exact fun hB => ih.1 hB
        · intro hs
          cases hatom with
          | mk hpp hn =>
              rw [WV_plays]
              exact Or.inr (hs _ _ (Pf.atom ⟨hpp, hn⟩))
      case pAtomNeg =>
        intro k0 p q b aN m0 hatom hne hle ih
        constructor
        · intro hB hEx
          obtain ⟨n', hn'⟩ := hEx
          obtain ⟨cert, hcle⟩ := hatom
          have hszpos : 1 ≤ (Formula.neg (.plays p q aN)).size := by
            simp only [Formula.size]; omega
          obtain ⟨N, hN⟩ := hplays p q p b _ cert (by omega)
          have h1 : eval (max N n') p q p = some b := eval_mono_le hN _ (Nat.le_max_left _ _)
          have h2 : eval (max N n') p q p = some aN :=
            eval_mono_le (show eval n' p q p = some aN from hn') _ (Nat.le_max_right _ _)
          rw [h1] at h2
          injection h2 with h3
          exact hne h3
        · intro hs
          rw [WV_neg, WV_plays]
          rintro (⟨rfl, hSP⟩ | hint)
          · cases b with
            | C => exact hne rfl
            | D => exact ih.2 hs p q hSP rfl
          · have hns := hs _ _ (Pf.atomNeg p q b aN m0 hatom hne hle)
            simp only [Formula.interp] at hns
            exact hns hint
      case pSearchBranch =>
        intro k0 g ψ a b me opponent hme hle
        constructor
        · intro _hB
          subst hme
          intro hguard
          have hps : proofSearch g
              (ψ.subst (.search g ψ (.const a) (.const b)) opponent) = true :=
            (proofSearch_spec _ _).2 hguard
          exact ⟨2, by simp only [play, eval, hps, if_true]⟩
        · intro hs
          rw [WV_impl, WV_box]
          intro hbox
          rw [WV_plays]
          exact Or.inr ((hs _ _ (Pf.searchBranch g ψ a b me opponent hme hle)) hbox)
      case pSimStep =>
        intro k0 me p q opponent a hme hle
        constructor
        · intro _hB
          subst hme
          rintro ⟨n, hn⟩
          exact ⟨n + 1, by show eval (n+1) (.sim p q) opponent (.sim p q) = some a
                           simp only [eval]; exact hn⟩
        · intro hs
          rw [WV_impl, WV_plays, WV_plays]
          rintro (⟨rfl, hSP⟩ | hint)
          · subst hme
            exact Or.inl ⟨rfl, h_simS p q opponent hSP⟩
          · exact Or.inr ((hs _ _ (Pf.simStep me p q opponent a hme hle)) hint)
      case pBotSimStep =>
        intro k0 me p q opponent a hme hle
        constructor
        · intro _hB
          subst hme
          rintro ⟨n, hn⟩
          exact ⟨n + 2, by
            show eval (n+2) (.bot (.sim p q)) opponent (.bot (.sim p q)) = some a
            simp only [eval]; exact hn⟩
        · intro hs
          rw [WV_impl, WV_plays, WV_plays]
          rintro (⟨rfl, hSP⟩ | hint)
          · subst hme
            exact Or.inl ⟨rfl, h_botsimS p q opponent hSP⟩
          · exact Or.inr ((hs _ _ (Pf.botSimStep me p q opponent a hme hle)) hint)
      case pBotSearchStep =>
        intro k0 g ψ a b me opponent hme hle
        constructor
        · intro _hB
          subst hme
          intro hguard
          have hps : proofSearch g
              (ψ.subst (.bot (.search g ψ (.const a) (.const b))) opponent) = true :=
            (proofSearch_spec _ _).2 hguard
          exact ⟨3, by simp only [play, eval, hps, if_true]⟩
        · intro hs
          rw [WV_impl, WV_box]
          intro hbox
          rw [WV_plays]
          exact Or.inr ((hs _ _ (Pf.botSearchStep g ψ a b me opponent hme hle)) hbox)
      case pIteBranchSearch =>
        intro k0 g z a' c0 c1 ψ q me opponent hme hle
        constructor
        · intro _hB
          subst hme
          rintro ⟨nb, hb⟩ hbox
          have hps : proofSearch g (ψ.subst
              (.ite (.sim .opp (.bot z)) a' (.search g ψ (.const c0) (.const c1)) q)
              opponent) = true := (proofSearch_spec _ _).2 hbox
          obtain ⟨m, rfl⟩ : ∃ m, nb = m + 1 := by
            cases nb with
            | zero => simp [play, eval] at hb
            | succ m => exact ⟨m, rfl⟩
          have hguard : eval (m + 1) opponent (.bot z) opponent = some a' := hb
          have hrefl : (a' == a') = true := by cases a' <;> rfl
          refine ⟨m + 1 + 1 + 1, ?_⟩
          show eval (m + 1 + 1 + 1) _ opponent _ = some c0
          rw [eval]
          simp only [bind, Option.bind]
          rw [show eval (m + 1 + 1) ((Prog.opp.sim z.bot).ite a'
                  (.search g ψ (.const c0) (.const c1)) q) opponent (.sim .opp (.bot z))
                = eval (m + 1) opponent (.bot z) opponent from rfl, hguard]
          simp only [hrefl, hps, if_pos, eval]
        · intro hs
          rw [WV_impl, WV_impl, WV_box]
          intro hprobe hbox
          rw [WV_plays]
          exact Or.inr ((hs _ _
            (Pf.iteBranchSearch_t g z a' c0 c1 ψ q me opponent hme hle))
            (interp_of_WV_probe h_nb hprobe) hbox)
      case pSTS =>
        intro k0 k₁ k₂ m0 ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle _ih
        constructor
        · intro _hB
          subst hme
          intro hbox
          have hps₁ : proofSearch k₁ (ψ₁.subst
              (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opponent) = true :=
            (proofSearch_spec _ _).2 hbox
          have hps₂ : proofSearch k₂ (ψ₂.subst
              (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opponent) = true :=
            (proofSearch_spec _ _).2 (Pf_mono hprud hmk)
          exact ⟨3, by simp only [play, eval, hps₁, hps₂, if_true]⟩
        · intro hs
          rw [WV_impl, WV_box]
          intro hbox
          rw [WV_plays]
          exact Or.inr ((hs _ _
            (Pf.searchThenSearch_t k₁ k₂ m0 ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle))
            hbox)
      case pSearchChain =>
        intro k0 g₁ ψ₁ e₁ L a me opponent hme hle
        constructor
        · intro _hB
          subst hme
          intro hbox
          refine implChain_interp _ (fun hg => ?_)
          obtain ⟨n, hn⟩ := searchPlug_eval _ opponent a (((g₁, ψ₁, e₁)) :: L)
            (by
              intro ψ' hψ'
              rcases List.mem_cons.mp hψ' with h1 | h2
              · exact h1 ▸ hbox
              · exact hg ψ' h2)
          exact ⟨n, hn⟩
        · intro hs
          rw [WV_impl, WV_box]
          intro hbox
          exact WV_of_interp_searchChain me opponent a L
            ((hs _ _ (Pf.searchChain g₁ ψ₁ e₁ L a me opponent hme hle)) hbox)
      case pCtxChain =>
        intro k0 hd L a me opponent hme hle
        constructor
        · intro _hB
          subst hme
          exact implChain_interp
            (ctxGuards (ctxPlug (hd :: L) (.const a)) opponent (hd :: L))
            (fun hg => ctxPlug_eval _ opponent a (hd :: L) hg)
        · intro hs
          have hI := hs _ _ (Pf.ctxChain hd L a me opponent hme hle)
          cases hd with
          | searchL g ψ e =>
              simp only [ctxGuard] at hI ⊢
              rw [WV_impl, WV_box]
              intro hbox
              exact WV_of_interp_ctxChain h_nb me opponent a L (hI hbox)
          | iteL z aT other =>
              simp only [ctxGuard] at hI ⊢
              rw [WV_impl]
              intro hprobe
              exact WV_of_interp_ctxChain h_nb me opponent a L
                (hI (interp_of_WV_probe h_nb hprobe))
      case pEqRefl =>
        intro k0 p _hle
        exact ⟨fun _ => rfl, fun _ => by rw [WV_eq]⟩
      case pEqNeg =>
        intro k0 p q hne _hle
        exact ⟨fun _ => hne, fun _ => by rw [WV_neg, WV_eq]; exact hne⟩
      case pMp =>
        intro k0 m₁ m₂ A B0 _himp _hante hle ihimp ihante
        constructor
        · intro hB
          exact ihimp.1 (by omega) (ihante.1 (by omega))
        · intro hs
          have i1 := ihimp.2 hs
          rw [WV_impl] at i1
          exact i1 (ihante.2 hs)
      case pImplTrans =>
        intro k0 A B0 C a b _hab _hbc hle ihab ihbc
        constructor
        · intro hB
          exact fun h => ihbc.1 (by omega) (ihab.1 (by omega) h)
        · intro hs
          have i1 := ihab.2 hs
          have i2 := ihbc.2 hs
          rw [WV_impl] at i1 i2 ⊢
          exact fun hφ => i2 (i1 hφ)
      case pWeaken =>
        intro k0 A B0 m0 _hψ hle ih
        constructor
        · intro hB
          exact fun _ => ih.1 (by omega)
        · intro hs
          rw [WV_impl]
          exact fun _ => ih.2 hs
      case pImpS2 =>
        intro A B0 C m₁ m₂ K0 _h1 _h2 hle ih1 ih2
        constructor
        · intro hB
          exact fun hφ => (ih1.1 (by omega) hφ) (ih2.1 (by omega) hφ)
        · intro hs
          have i1 := ih1.2 hs
          have i2 := ih2.2 hs
          rw [WV_impl] at i1 i2 ⊢
          intro hφ
          have hi := i1 hφ
          rw [WV_impl] at hi
          exact hi (i2 hφ)
      case pImplRefl =>
        intro k0 A _hle
        exact ⟨fun _ h => h, fun _ => by rw [WV_impl]; exact id⟩
      case pImplK =>
        intro k0 A B0 _hle
        refine ⟨fun _ h _ => h, fun _ => ?_⟩
        rw [WV_impl]
        intro hφ
        rw [WV_impl]
        exact fun _ => hφ
      case pImplS =>
        intro k0 A B0 C0 _hle
        refine ⟨fun _ f g x => f x (g x), fun _ => ?_⟩
        rw [WV_impl]
        intro hf
        rw [WV_impl]
        intro hg
        rw [WV_impl]
        intro hx
        rw [WV_impl] at hf hg
        have h1 := hf hx
        rw [WV_impl] at h1
        exact h1 (hg hx)
      case pContrapose =>
        intro k0 A B0 m0 _h hle ih
        constructor
        · intro hB
          exact fun hn hp => hn (ih.1 (by omega) hp)
        · intro hs
          have i := ih.2 hs
          rw [WV_impl] at i
          rw [WV_impl, WV_neg, WV_neg]
          exact fun hnψ hφ => hnψ (i hφ)
      case pNegElim =>
        intro k0 A B0 m₁ m₂ _h1 _h2 hle ih1 ih2
        constructor
        · intro hB
          exact absurd (ih2.1 (by omega)) (ih1.1 (by omega))
        · intro hs
          have i1 := ih1.2 hs
          rw [WV_neg] at i1
          exact absurd (ih2.2 hs) i1
      case pBoxIntro =>
        intro kIn K0 A hprem _hle _ih
        exact ⟨fun _ => hprem, fun _ => by rw [WV_box]; exact hprem⟩
      case pAtomBoxImpl =>
        intro k0 kBox p q a hatom _hle _ih
        refine ⟨fun _ _ => Pf.atom hatom, fun _ => ?_⟩
        show WV S (.impl (.plays p q a) (.box kBox (.plays p q a)))
        rw [WV_impl, WV_box]
        exact fun _ => Pf.atom hatom
      case pAxK =>
        intro a b c m0 K0 A B0 _hprem hgate hle ih
        constructor
        · intro hB
          exact fun hφ => Pf.mp a b A B0 (ih.1 (by omega)) hφ hgate
        · intro hs
          have i := ih.2 hs
          rw [WV_box] at i
          rw [WV_impl, WV_box, WV_box]
          exact fun hb => Pf.mp a b A B0 i hb hgate
      case pAxKf =>
        intro a b c K0 A B0 hgate _hle
        refine ⟨fun _ hab ha => Pf.mp a b A B0 hab ha hgate, fun _ => ?_⟩
        rw [WV_impl, WV_box, WV_impl, WV_box, WV_box]
        exact fun h1 hb => Pf.mp a b A B0 h1 hb hgate
      case pBox4 =>
        intro a b K0 A hgate _hle
        refine ⟨fun _ hφ => Pf.boxIntro a b A hφ hgate, fun _ => ?_⟩
        rw [WV_impl, WV_box, WV_box]
        exact fun hp => Pf.boxIntro a b A hp hgate
      case pBoxMono =>
        intro a b K0 A hab _hle
        refine ⟨fun _ hpa => Pf_mono hpa hab, fun _ => ?_⟩
        rw [WV_impl, WV_box, WV_box]
        exact fun hp => Pf_mono hp hab
      case pDiagF =>
        intro pm fb g K0 tgt _hgate _hle _ih
        refine ⟨fun _ h => h, fun _ => ?_⟩
        rw [WV_impl, WV_diag, WV_impl, WV_box]
        exact fun hd => hd
      case pDiagB =>
        intro pm fb g K0 tgt _hgate _hle _ih
        refine ⟨fun _ h => h, fun _ => ?_⟩
        rw [WV_impl, WV_impl, WV_box, WV_diag]
        exact fun hd => hd
    exact ⟨hplays, hpf⟩

end PD.BaseTheorems
