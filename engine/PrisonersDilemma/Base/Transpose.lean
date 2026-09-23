import PrisonersDilemma.Program
import PrisonersDilemma.ProofSystem

/-!
# The C/D transposition τ — syntax layer + Pf-invariance (Thm 1.10)

Mechanization of `latex/Cupod_vs_Dupco_proof.tex`, Definitions 1.3 (constant
relabelling), 1.8 (the transposition `τ = (C D)`), and 1.11 (the source-code
transposition `τ̂`), specialized to the engine's `Prog`/`Formula` syntax.
Promoted 2026-08-20 from `Research/Spikes/transpose/` (audit history in that
folder's README/TOMBSTONES); consumed by `Theorems/DupocBot/vs_CupodBot.lean`
— the red cell, the matchup Critch–Dennis–Russell 2022 leave open.

`τ̂` is ONE structural map (mutual over `Prog`/`Formula`) that swaps the two
action constants everywhere — in `.const` leaves, `.ite` selectors, `.plays`
atoms — and leaves all budgets, all structure, and all names untouched. Three
properties carry the whole paper argument, each proved here:

* **involution** (`transpose_transpose`) — Def 1.8's `τ ∘ τ = id`;
* **length preservation** (`size_transpose`) — the paper's "equal encoding
  length" hypothesis (Thm 1.10's length clause). In the engine it is EXACT:
  `Action.C` and `Action.D` are single constructors of the same size-1 cost,
  and τ̂ touches nothing else.
* **equivariance of substitution** (`subst_transpose`) — the paper's
  τ-equivariant Gödel encoding (Prop 1.12's hypothesis
  `⌜τ̂(s)⌝ = (⌜s⌝)^τ`): here quotation is the identity (formulas carry
  programs directly), so equivariance becomes commutation with `subst`,
  the engine's context-closing operation.

## The ONE deliberate freeze: `.tvote` entries

`τ̂` does NOT descend into `VoteList` entries, mirroring `Prog.subst` (entries
are frozen closed instances). This is forced, not cosmetic: the action-vote
primitive is intrinsically C/D-ASYMMETRIC — an entry fires iff it plays `C`
(`eval`'s peel, `PlaysProof.voteCons_c`), so transposing inside an entry flips
its vote and `Pf`-invariance dies at the `voteCons_*` arms. With frozen
entries every vote rule transposes verbatim (the entry certificates are reused
untouched). `.tvote` is a tau-layer extension, not part of the paper's
language; on the paper's fragment (everything Dupoc/Cupod contain) τ̂ is the
full literal source transposition.
-/

namespace PD

/-- Def 1.8: the constant transposition `τ = (C D)` on actions. -/
def Action.swap : Action → Action
  | .C => .D
  | .D => .C

@[simp] theorem Action.swap_swap : ∀ a : Action, a.swap.swap = a := by
  intro a; cases a <;> rfl

theorem Action.swap_inj : ∀ {a b : Action}, a.swap = b.swap → a = b := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem Action.swap_ne : ∀ {a b : Action}, a ≠ b → a.swap ≠ b.swap :=
  fun h hc => h (Action.swap_inj hc)

/-- τ commutes with the boolean action test (used by the `.ite` transcript rules). -/
theorem Action.swap_beq : ∀ a b : Action, (a.swap == b.swap) = (a == b) := by
  intro a b; cases a <;> cases b <;> rfl

mutual
  /-- Def 1.11: the source-code transposition `τ̂` on programs. Swaps the action
      constants everywhere except inside frozen `VoteList` entries (see header). -/
  def Prog.transpose : Prog → Prog
    | .const a        => .const a.swap
    | .self           => .self
    | .opp            => .opp
    | .bot p          => .bot p.transpose
    | .sim p q        => .sim p.transpose q.transpose
    | .ite b a p q    => .ite b.transpose a.swap p.transpose q.transpose
    | .search k φ p q => .search k φ.transpose p.transpose q.transpose
    | .tvote v θ p q  => .tvote v θ p.transpose q.transpose
    | .sys defs i     => .sys defs.transpose i
    | .selfIdx j      => .selfIdx j         -- a bare reference carries no action

  /-- τ̂ on a system's member list. Unlike `.tvote` entries (frozen — their FIRING
      is C-asymmetric, see the header), a system member is an ordinary program whose
      action constants must flip; freezing them would leave `Pf.transpose`'s
      `sysStep` arm without a Lean proof (the premise transposes the closed component, so the
      member list must transpose with it). -/
  def ProgList.transpose : ProgList → ProgList
    | .nil         => .nil
    | .cons p rest => .cons p.transpose rest.transpose

  /-- Def 1.3/1.8: constant relabelling `φ^τ` on formulas — replaces every `C`
      by `D` and vice versa, commuting with every logical symbol (eq. (1.1)). -/
  def Formula.transpose : Formula → Formula
    | .plays p q a => .plays p.transpose q.transpose a.swap
    | .impl φ ψ    => .impl φ.transpose ψ.transpose
    | .neg φ       => .neg φ.transpose
    | .box n φ     => .box n φ.transpose
    | .eq p q      => .eq p.transpose q.transpose
    | .diag g φ    => .diag g φ.transpose
end

/-! ## τ̂ is an involution (Def 1.8: `τ ∘ τ = id`) -/

mutual
  @[simp] theorem Prog.transpose_transpose : ∀ p : Prog, p.transpose.transpose = p
    | .const a        => by simp [Prog.transpose]
    | .self           => rfl
    | .opp            => rfl
    | .bot p          => by simp [Prog.transpose, Prog.transpose_transpose p]
    | .sim p q        => by
        simp [Prog.transpose, Prog.transpose_transpose p, Prog.transpose_transpose q]
    | .ite b a p q    => by
        simp [Prog.transpose, Prog.transpose_transpose b, Prog.transpose_transpose p,
          Prog.transpose_transpose q]
    | .search k φ p q => by
        simp [Prog.transpose, Formula.transpose_transpose φ, Prog.transpose_transpose p,
          Prog.transpose_transpose q]
    | .tvote v θ p q  => by
        simp [Prog.transpose, Prog.transpose_transpose p, Prog.transpose_transpose q]
    | .sys defs i     => by
        simp [Prog.transpose, ProgList.transpose_transpose defs]
    | .selfIdx j      => rfl

  @[simp] theorem ProgList.transpose_transpose :
      ∀ l : ProgList, l.transpose.transpose = l
    | .nil         => rfl
    | .cons p rest => by
        simp [ProgList.transpose, Prog.transpose_transpose p,
          ProgList.transpose_transpose rest]

  @[simp] theorem Formula.transpose_transpose : ∀ φ : Formula, φ.transpose.transpose = φ
    | .plays p q a => by
        simp [Formula.transpose, Prog.transpose_transpose p, Prog.transpose_transpose q]
    | .impl φ ψ    => by
        simp [Formula.transpose, Formula.transpose_transpose φ, Formula.transpose_transpose ψ]
    | .neg φ       => by simp [Formula.transpose, Formula.transpose_transpose φ]
    | .box n φ     => by simp [Formula.transpose, Formula.transpose_transpose φ]
    | .eq p q      => by
        simp [Formula.transpose, Prog.transpose_transpose p, Prog.transpose_transpose q]
    | .diag g φ    => by simp [Formula.transpose, Formula.transpose_transpose φ]
end

theorem Prog.transpose_inj {p q : Prog} (h : p.transpose = q.transpose) : p = q := by
  have := congrArg Prog.transpose h
  simpa using this

theorem Prog.transpose_ne {p q : Prog} (h : p ≠ q) : p.transpose ≠ q.transpose :=
  fun hc => h (Prog.transpose_inj hc)

/-! ## τ̂ preserves length exactly (Thm 1.10's "equal encoding length" clause)

The engine's `size` is the character count the budgets are measured in; τ̂
only exchanges two same-cost constants, so every program and formula keeps its
size — hence every proof transcript keeps its budget, with NO `+c` splice. -/

mutual
  @[simp] theorem Prog.size_transpose : ∀ p : Prog, p.transpose.size = p.size
    | .const _        => rfl
    | .self           => rfl
    | .opp            => rfl
    | .bot p          => by simp [Prog.transpose, Prog.size, Prog.size_transpose p]
    | .sim p q        => by
        simp [Prog.transpose, Prog.size, Prog.size_transpose p, Prog.size_transpose q]
    | .ite b a p q    => by
        simp [Prog.transpose, Prog.size, Prog.size_transpose b, Prog.size_transpose p,
          Prog.size_transpose q]
    | .search k φ p q => by
        simp [Prog.transpose, Prog.size, Formula.size_transpose φ, Prog.size_transpose p,
          Prog.size_transpose q]
    | .tvote v θ p q  => by
        simp [Prog.transpose, Prog.size, Prog.size_transpose p, Prog.size_transpose q]
    | .sys defs i     => by
        simp [Prog.transpose, Prog.size, ProgList.psize_transpose defs]
    | .selfIdx j      => rfl

  @[simp] theorem ProgList.psize_transpose :
      ∀ l : ProgList, l.transpose.psize = l.psize
    | .nil         => rfl
    | .cons p rest => by
        simp [ProgList.transpose, ProgList.psize, Prog.size_transpose p,
          ProgList.psize_transpose rest]

  @[simp] theorem Formula.size_transpose : ∀ φ : Formula, φ.transpose.size = φ.size
    | .plays p q _ => by
        simp [Formula.transpose, Formula.size, Prog.size_transpose p, Prog.size_transpose q]
    | .impl φ ψ    => by
        simp [Formula.transpose, Formula.size, Formula.size_transpose φ,
          Formula.size_transpose ψ]
    | .neg φ       => by simp [Formula.transpose, Formula.size, Formula.size_transpose φ]
    | .box n φ     => by simp [Formula.transpose, Formula.size, Formula.size_transpose φ]
    | .eq p q      => by
        simp [Formula.transpose, Formula.size, Prog.size_transpose p, Prog.size_transpose q]
    | .diag g φ    => by simp [Formula.transpose, Formula.size, Formula.size_transpose φ]
end

/-! ## τ̂ is substitution-equivariant (Prop 1.12's encoding hypothesis)

`subst` is the engine's quotation boundary (placeholders freeze to concrete
sources), so the paper's `⌜τ̂(s)⌝ = (⌜s⌝)^τ` becomes: transposing a closed
instance = instantiating the transposed template with transposed players. -/

mutual
  @[simp] theorem Prog.subst_transpose :
      ∀ (p me opponent : Prog),
        (p.subst me opponent).transpose
          = p.transpose.subst me.transpose opponent.transpose
    | .const a,        _,  _ => rfl
    | .self,           _,  _ => rfl
    | .opp,            _,  _ => rfl
    | .bot p,          _,  _ => rfl
    | .sim p q,        me, o => by
        simp [Prog.subst, Prog.transpose, Prog.subst_transpose p me o,
          Prog.subst_transpose q me o]
    | .ite b a p q,    me, o => by
        simp [Prog.subst, Prog.transpose, Prog.subst_transpose b me o,
          Prog.subst_transpose p me o, Prog.subst_transpose q me o]
    | .search k φ p q, me, o => by
        simp [Prog.subst, Prog.transpose, Formula.subst_transpose φ me o,
          Prog.subst_transpose p me o, Prog.subst_transpose q me o]
    | .tvote v θ p q,  me, o => by
        simp [Prog.subst, Prog.transpose, Prog.subst_transpose p me o,
          Prog.subst_transpose q me o]
    | .sys defs i,     _,  _ => rfl
    | .selfIdx j,      _,  _ => rfl

  @[simp] theorem Formula.subst_transpose :
      ∀ (φ : Formula) (me opponent : Prog),
        (φ.subst me opponent).transpose
          = φ.transpose.subst me.transpose opponent.transpose
    | .plays p q a, me, o => by
        simp [Formula.subst, Formula.transpose, Prog.subst_transpose p me o,
          Prog.subst_transpose q me o]
    | .impl φ ψ,    me, o => by
        simp [Formula.subst, Formula.transpose, Formula.subst_transpose φ me o,
          Formula.subst_transpose ψ me o]
    | .neg φ,       me, o => by
        simp [Formula.subst, Formula.transpose, Formula.subst_transpose φ me o]
    | .box n φ,     me, o => by
        simp [Formula.subst, Formula.transpose, Formula.subst_transpose φ me o]
    | .eq p q,      me, o => by
        simp [Formula.subst, Formula.transpose, Prog.subst_transpose p me o]
    | .diag g φ,    _,  _ => rfl
end

/-! ## τ̂ commutes with the SYSTEM-level closer

The binder's counterpart to `subst_transpose`, and the one place where `.sys`
DIFFERS from `.tvote`: τ̂ descends into system MEMBERS (a member is an ordinary
program whose actions flip) while it freezes vote ENTRIES (whose firing is
C-asymmetric — see the header). Consequently the equivariance carries the
transposed system: closing with `defs` then transposing equals transposing then
closing with `defs.transpose`. Freezing members instead was tried and leaves
`Pf.transpose`'s `sysStep` arm without a Lean proof — the premise transposes the closed
component, so the member list must transpose with it. -/

/-- τ̂ preserves member lookup: transposing a system transposes the member found at
    each index. The `sysStep` arm needs it to rebuild `hget` on the τ̂ side. -/
@[simp] theorem ProgList.get?_transpose :
    ∀ (l : ProgList) (i : Nat) (p : Prog), l.get? i = some p →
      l.transpose.get? i = some p.transpose
  | .nil,         _,     _, h => by simp [ProgList.get?] at h
  | .cons q _,    0,     p, h => by
      simp only [ProgList.get?, Option.some.injEq] at h
      simp [ProgList.transpose, ProgList.get?, h]
  | .cons _ rest, n + 1, p, h => by
      simp only [ProgList.get?] at h
      simpa [ProgList.transpose, ProgList.get?] using
        ProgList.get?_transpose rest n p h

mutual
  @[simp] theorem Prog.sysClose_transpose :
      ∀ (p : Prog) (defs : ProgList),
        (p.sysClose defs).transpose = p.transpose.sysClose defs.transpose
    | .const a,        _ => rfl
    | .self,           _ => rfl
    | .opp,            _ => rfl
    | .bot p,          d => by
        simp [Prog.sysClose, Prog.transpose, Prog.sysClose_transpose p d]
    | .sim p q,        d => by
        simp [Prog.sysClose, Prog.transpose, Prog.sysClose_transpose p d,
          Prog.sysClose_transpose q d]
    | .ite b a p q,    d => by
        simp [Prog.sysClose, Prog.transpose, Prog.sysClose_transpose b d,
          Prog.sysClose_transpose p d, Prog.sysClose_transpose q d]
    | .search k φ p q, d => by
        simp [Prog.sysClose, Prog.transpose, Formula.sysClose_transpose φ d,
          Prog.sysClose_transpose p d, Prog.sysClose_transpose q d]
    | .tvote v θ p q,  d => by
        -- entries are frozen for τ̂ but NOT for `sysClose`; the branches commute
        simp [Prog.sysClose, Prog.transpose, Prog.sysClose_transpose p d,
          Prog.sysClose_transpose q d]
    | .sys dl i,       _ => rfl
    | .selfIdx j,      _ => rfl
  termination_by structural p => p

  @[simp] theorem Formula.sysClose_transpose :
      ∀ (φ : Formula) (defs : ProgList),
        (φ.sysClose defs).transpose = φ.transpose.sysClose defs.transpose
    | .plays p q a, d => by
        simp [Formula.sysClose, Formula.transpose, Prog.sysClose_transpose p d,
          Prog.sysClose_transpose q d]
    | .impl φ ψ,    d => by
        simp [Formula.sysClose, Formula.transpose, Formula.sysClose_transpose φ d,
          Formula.sysClose_transpose ψ d]
    | .neg φ,       d => by
        simp [Formula.sysClose, Formula.transpose, Formula.sysClose_transpose φ d]
    | .box n φ,     d => by
        simp [Formula.sysClose, Formula.transpose, Formula.sysClose_transpose φ d]
    | .eq p q,      d => by
        simp [Formula.sysClose, Formula.transpose, Prog.sysClose_transpose p d,
          Prog.sysClose_transpose q d]
    | .diag g φ,    d => by
        simp [Formula.sysClose, Formula.transpose, Formula.sysClose_transpose φ d]
  termination_by structural f => f
end


/-! ## τ̂ on the telescope layer lists

The three Family-A chain rules (`searchChain`, `ctxChain`, `searchElseChain`)
quantify over layer LISTS; τ̂ maps them pointwise and commutes with every
plug/guard/cost function. Budgets and costs are untouched (length
preservation, again exact). -/

/-- τ̂ on a `searchChain` layer list. -/
def tSearchLayer (l : Nat × Formula × Prog) : Nat × Formula × Prog :=
  (l.1, l.2.1.transpose, l.2.2.transpose)

@[simp] theorem searchPlug_transpose (L : List (Nat × Formula × Prog)) (p : Prog) :
    (searchPlug L p).transpose = searchPlug (L.map tSearchLayer) p.transpose := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨g, ψ, e⟩ := hd
      simp [searchPlug, Prog.transpose, tSearchLayer, ih]

@[simp] theorem searchGuards_transpose (me opponent : Prog)
    (L : List (Nat × Formula × Prog)) :
    (searchGuards me opponent L).map Formula.transpose
      = searchGuards me.transpose opponent.transpose (L.map tSearchLayer) := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨g, ψ, e⟩ := hd
      simp [searchGuards, Formula.transpose, tSearchLayer, ih]

@[simp] theorem implChain_transpose (gs : List Formula) (tgt : Formula) :
    (implChain gs tgt).transpose = implChain (gs.map Formula.transpose) tgt.transpose := by
  induction gs with
  | nil => rfl
  | cons hd tl ih =>
      simp only [implChain, List.map_cons, List.foldr_cons, Formula.transpose] at ih ⊢
      rw [ih]

/-- τ̂ on a `ctxChain` layer. -/
def CtxLayer.transpose : CtxLayer → CtxLayer
  | .searchL g ψ e   => .searchL g ψ.transpose e.transpose
  | .iteL z aT other => .iteL z.transpose aT.swap other.transpose

@[simp] theorem ctxPlug_transpose (L : List CtxLayer) (p : Prog) :
    (ctxPlug L p).transpose = ctxPlug (L.map CtxLayer.transpose) p.transpose := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
      cases hd <;> simp [ctxPlug, Prog.transpose, CtxLayer.transpose, ih]

@[simp] theorem ctxGuard_transpose (me opponent : Prog) (l : CtxLayer) :
    (ctxGuard me opponent l).transpose
      = ctxGuard me.transpose opponent.transpose l.transpose := by
  cases l <;> simp [ctxGuard, Formula.transpose, CtxLayer.transpose, Prog.transpose]

@[simp] theorem ctxGuards_transpose (me opponent : Prog) (L : List CtxLayer) :
    (ctxGuards me opponent L).map Formula.transpose
      = ctxGuards me.transpose opponent.transpose (L.map CtxLayer.transpose) := by
  induction L with
  | nil => rfl
  | cons hd tl ih => simp [ctxGuards, ih, ctxGuard_transpose]

/-- τ̂ on a `searchElseChain` layer. -/
def SearchLayer2.transpose : SearchLayer2 → SearchLayer2
  | .thenL g ψ e     => .thenL g ψ.transpose e.transpose
  | .elseL g P Q c p => .elseL g P.transpose Q.transpose c.swap p.transpose

@[simp] theorem plug2_transpose (L : List SearchLayer2) (p : Prog) :
    (plug2 L p).transpose = plug2 (L.map SearchLayer2.transpose) p.transpose := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
      cases hd <;>
        simp [plug2, Prog.transpose, Formula.transpose, SearchLayer2.transpose, ih]

@[simp] theorem guard2_transpose (me opponent : Prog) (l : SearchLayer2) :
    (guard2 me opponent l).transpose
      = guard2 me.transpose opponent.transpose l.transpose := by
  cases l <;> simp [guard2, Formula.transpose, SearchLayer2.transpose]

@[simp] theorem guards2_transpose (me opponent : Prog) (L : List SearchLayer2) :
    (guards2 me opponent L).map Formula.transpose
      = guards2 me.transpose opponent.transpose (L.map SearchLayer2.transpose) := by
  induction L with
  | nil => rfl
  | cons hd tl ih => simp [guards2, ih, guard2_transpose]

/-- Layer costs never see the action constants — the "equal encoding length"
    clause at the telescope tier. -/
@[simp] theorem layersCost_transpose (L : List SearchLayer2) :
    layersCost (L.map SearchLayer2.transpose) = layersCost L := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
      cases hd <;> simp [layersCost, layerCost, SearchLayer2.transpose, ih]



/-!
# Theorem 1.10 — transposition invariance of `S`-provability (`⊢_k`), at the SAME budget

`Pf k φ → Pf k φ^τ`, by ONE joint induction over the whole mutual proof-term
block (`PlaysProof`/`VoteAllPlay`/`AtomProvable`/`Pf`). This is the paper's
Theorem 1.10 with its LENGTH clause built in: because the engine's `S` is
presented as a constructor-closed rule set whose every side-condition measures
sizes that τ̂ preserves EXACTLY (`size_transpose`), the transposed proof term
is literally a proof term of the same transcript budget — the "no splices"
case of the paper's proof, with no `+c` slack anywhere. The paper's automorphism
hypothesis (Def 1.9: every nonlogical axiom maps to an axiom) is discharged
arm by arm: each of the 30 `Pf` rules, 14 transcript rules, and the two bridge
types is closed under τ̂.

Two arms carry the interesting content:

* the vote arms (`voteCons_c/d`, `voteHigh_f`): sound ONLY because τ̂ freezes
  `VoteList` entries (see the syntax-layer header above) — the entry certificates
  are reused verbatim, untouched by the induction;
* `diagF`/`diagB`: the Löb fixpoint commutes with τ̂ syntactically
  (`(.diag g tgt)^τ = .diag g tgt^τ`), so the bounded-Löb machinery transposes
  with no extra argument — the fixpoint construction itself is C/D-blind.

The raw `Pf.rec` is deliberate (the one sanctioned use-case, as in
`Base/ValuationSoundness`): the `atom` bridge needs the `AtomProvable` motive,
whose `mk` needs the `PlaysProof` motive, whose `search_t/search_f` need the
`Pf` motive back — all four must ride together.
-/


/-- **Theorem 1.10 (bounded transposition invariance)**: a ≤`k`-character `S`-derivation
    of `φ` transposes to a ≤`k`-character `S`-derivation of `φ^τ`. Same budget — the
    equal-encoding-length hypothesis holds exactly in this syntax. -/
theorem Pf.transpose {k : Nat} {φ : Formula} (h : Pf k φ) : Pf k φ.transpose :=
  Pf.rec
    (motive_1 := fun me opponent body a n _ =>
      PlaysProof me.transpose opponent.transpose body.transpose a.swap n)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun k φ _ => AtomProvable k φ.transpose)
    (motive_4 := fun k φ _ => Pf k φ.transpose)
    -- ── PlaysProof arms (14): the transcript transposes step for step ──
    -- const
    (by intro me opponent a
        simp only [Prog.transpose]
        exact PlaysProof.const)
    -- self
    (fun _ ih => by
        simp only [Prog.transpose]
        exact PlaysProof.self ih)
    -- opp
    (fun _ ih => by
        simp only [Prog.transpose]
        exact PlaysProof.opp ih)
    -- bot
    (fun _ ih => by
        simp only [Prog.transpose]
        exact PlaysProof.bot ih)
    -- sim
    (fun _ ih => by
        simp only [Prog.transpose, Prog.subst_transpose] at ih ⊢
        exact PlaysProof.sim ih)
    -- ite_t
    (fun _ hr _ ihb ihp => by
        simp only [Prog.transpose]
        exact PlaysProof.ite_t ihb (by rw [Action.swap_beq]; exact hr) ihp)
    -- ite_f
    (fun _ hr _ ihb ihq => by
        simp only [Prog.transpose]
        exact PlaysProof.ite_f ihb (by rw [Action.swap_beq]; exact hr) ihq)
    -- search_t
    (fun _ _ ihg ihp => by
        simp only [Prog.transpose]
        simp only [Formula.subst_transpose] at ihg
        exact PlaysProof.search_t ihg ihp)
    -- search_f
    (fun _ _ ihg ihq => by
        simp only [Prog.transpose]
        simp only [Formula.transpose, Formula.subst_transpose] at ihg
        exact PlaysProof.search_f ihg ihq)
    -- voteZero_t (entries frozen: the vote list rides along untouched)
    (fun _ ihp => by
        simp only [Prog.transpose] at ihp ⊢
        exact PlaysProof.voteZero_t ihp)
    -- voteNil_f
    (fun hθ _ ihq => by
        simp only [Prog.transpose] at ihq ⊢
        exact PlaysProof.voteNil_f hθ ihq)
    -- voteCons_c: reuse the head entry's certificate VERBATIM (`hI`) — this is
    -- where descending into the entry would flip the vote and kill the theorem
    (fun hθ hI _ _ ihp => by
        simp only [Prog.transpose] at ihp ⊢
        exact PlaysProof.voteCons_c hθ hI ihp)
    -- voteCons_d
    (fun hθ hI _ _ ihq => by
        simp only [Prog.transpose] at ihq ⊢
        exact PlaysProof.voteCons_d hθ hI ihq)
    -- voteHigh_f: termination evidence `hterm` reused verbatim, cost untouched
    (fun hθ hterm _ _ ihq => by
        simp only [Prog.transpose] at ihq ⊢
        exact PlaysProof.voteHigh_f hθ hterm ihq)
    -- sysStep: `.sys` is FROZEN under τ̂ (like `.tvote` entries), so the system and
    -- its index survive verbatim; only the CLOSED COMPONENT in the premise
    -- transposes, and `sysClose` commutes with τ̂ because both freeze the binder.
    (fun {me opponent} {defs} {i} {p} {a} {n} hget _h ih => by
        simp only [Prog.transpose, Prog.sysClose_transpose] at ih ⊢
        exact PlaysProof.sysStep (ProgList.get?_transpose defs i p hget) ih)
    -- ── VoteAllPlay arms (2): motive is `True` (entries are frozen) ──
    trivial
    (fun _ _ _ _ => trivial)
    -- ── AtomProvable arm (1): the bridge transposes by transposing its transcript ──
    (fun _ hle ihcert => by
        simp only [Formula.transpose]
        exact AtomProvable.mk ihcert hle)
    -- ── Pf arms (30, family order A/B/C) ──
    -- atom
    (fun _ ihatom => Pf.atom ihatom)
    -- atomNeg
    (fun p q b aN m _ hne hle ihatom => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ihatom ⊢
        exact Pf.atomNeg p.transpose q.transpose b.swap aN.swap m ihatom
          (Action.swap_ne hne) hle)
    -- searchBranch
    (fun g ψ a b me opponent hme hle => by
        subst hme
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose, Prog.transpose, Formula.subst_transpose] at hle ⊢
        exact Pf.searchBranch g ψ.transpose a.swap b.swap _ opponent.transpose rfl hle)
    -- simStep
    (fun me p q opponent a hme hle => by
        subst hme
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose, Prog.transpose, Prog.subst_transpose] at hle ⊢
        exact Pf.simStep _ p.transpose q.transpose opponent.transpose a.swap rfl hle)
    -- botSimStep
    (fun me p q opponent a hme hle => by
        subst hme
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose, Prog.transpose, Prog.subst_transpose] at hle ⊢
        exact Pf.botSimStep _ p.transpose q.transpose opponent.transpose a.swap rfl hle)
    -- botSearchStep
    (fun g ψ a b me opponent hme hle => by
        subst hme
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose, Prog.transpose, Formula.subst_transpose] at hle ⊢
        exact Pf.botSearchStep g ψ.transpose a.swap b.swap _ opponent.transpose rfl hle)
    -- botSysSearchStep: τ̂ descends into system members, so the transposed component
    -- sits at the same index (`get?_transpose`) and its guard closes with the
    -- transposed system (`sysClose_transpose`)
    (fun defs i g ψ a b me opponent hme hget hle => by
        subst hme
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose, Prog.transpose, Formula.subst_transpose,
          Formula.sysClose_transpose] at hle ⊢
        exact Pf.botSysSearchStep defs.transpose i g ψ.transpose a.swap b.swap _
          opponent.transpose rfl
          (by simpa [Prog.transpose] using ProgList.get?_transpose defs i _ hget) hle)
    -- botSysSimStep: same descent as botSysSearchStep — the transposed copy
    -- component sits at the same index, and its frozen `.selfIdx` operands
    -- transpose to themselves
    (fun defs i j a me opponent hme hget hle => by
        subst hme
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose, Prog.transpose] at hle ⊢
        exact Pf.botSysSimStep defs.transpose i j a.swap _ opponent.transpose rfl
          (by simpa [Prog.transpose] using ProgList.get?_transpose defs i _ hget) hle)
    -- botSysSearchThenSearch: the nested descent inside the binder
    (fun defs i k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hget hprud hmk hle ih => by
        subst hme
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose, Prog.transpose, Formula.subst_transpose,
          Formula.sysClose_transpose] at hle ih ⊢
        exact Pf.botSysSearchThenSearch defs.transpose i k₁ k₂ m ψ₁.transpose ψ₂.transpose
          c0.swap c1.swap q.transpose _ opponent.transpose rfl
          (by simpa [Prog.transpose] using ProgList.get?_transpose defs i _ hget) ih hmk hle)
    -- iteBranchSearch_t
    (fun g z a' c0 c1 ψ q me opponent hme hle => by
        subst hme
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose, Prog.transpose, Formula.subst_transpose] at hle ⊢
        exact Pf.iteBranchSearch_t g z.transpose a'.swap c0.swap c1.swap ψ.transpose
          q.transpose _ opponent.transpose rfl hle)
    -- searchThenSearch_t
    (fun k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle ih => by
        subst hme
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose, Prog.transpose, Formula.subst_transpose] at hle ih ⊢
        exact Pf.searchThenSearch_t k₁ k₂ m ψ₁.transpose ψ₂.transpose c0.swap c1.swap
          q.transpose _ opponent.transpose rfl ih hmk hle)
    -- searchChain
    (fun g₁ ψ₁ e₁ L a me opponent hme hle => by
        subst hme
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose, Prog.transpose, Formula.subst_transpose,
          searchPlug_transpose, searchGuards_transpose, implChain_transpose] at hle ⊢
        exact Pf.searchChain g₁ ψ₁.transpose e₁.transpose (L.map tSearchLayer) a.swap
          _ opponent.transpose rfl hle)
    -- ctxChain
    (fun hd L a me opponent hme hle => by
        subst hme
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose, Prog.transpose,
          ctxPlug_transpose, ctxGuard_transpose, ctxGuards_transpose, implChain_transpose,
          List.map_cons] at hle ⊢
        exact Pf.ctxChain hd.transpose (L.map CtxLayer.transpose) a.swap
          _ opponent.transpose rfl hle)
    -- eqRefl
    (fun p hle => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ⊢
        exact Pf.eqRefl p.transpose hle)
    -- eqNeg
    (fun p q hne hle => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ⊢
        exact Pf.eqNeg p.transpose q.transpose (Prog.transpose_ne hne) hle)
    -- mp
    (fun m₁ m₂ φ α _ _ hle ih1 ih2 => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at ih1
        exact Pf.mp m₁ m₂ φ.transpose α.transpose ih1 ih2 hle)
    -- implTrans
    (fun φ ψ χ a b _ _ hle ih1 ih2 => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ih1 ih2 ⊢
        exact Pf.implTrans φ.transpose ψ.transpose χ.transpose a b ih1 ih2 hle)
    -- weakenImpl
    (fun φ ψ m _ hle ih => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ⊢
        exact Pf.weakenImpl φ.transpose ψ.transpose m ih hle)
    -- impS2
    (fun φ ψ χ m₁ m₂ K _ _ hle ih1 ih2 => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ih1 ih2 ⊢
        exact Pf.impS2 φ.transpose ψ.transpose χ.transpose m₁ m₂ K ih1 ih2 hle)
    -- implRefl
    (fun φ hle => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ⊢
        exact Pf.implRefl φ.transpose hle)
    -- implK
    (fun φ ψ hle => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ⊢
        exact Pf.implK φ.transpose ψ.transpose hle)
    -- implS
    (fun φ ψ χ hle => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ⊢
        exact Pf.implS φ.transpose ψ.transpose χ.transpose hle)
    -- contrapose
    (fun φ ψ m _ hle ih => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ih ⊢
        exact Pf.contrapose φ.transpose ψ.transpose m ih hle)
    -- negElim
    (fun φ ψ m₁ m₂ _ _ hle ih1 ih2 => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at ih1
        exact Pf.negElim φ.transpose ψ.transpose m₁ m₂ ih1 ih2 hle)
    -- boxIntro
    (fun kIn K φ _ hle ih => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ⊢
        exact Pf.boxIntro kIn K φ.transpose ih hle)
    -- atomBoxImpl
    (fun kBox p q a _ hle ihatom => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ihatom ⊢
        exact Pf.atomBoxImpl kBox p.transpose q.transpose a.swap ihatom hle)
    -- axK
    (fun a b c m K φ α _ hgate hle ih => by
        rw [← Formula.size_transpose] at hgate
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ih ⊢
        exact Pf.axK a b c m K φ.transpose α.transpose ih hgate hle)
    -- axKf
    (fun a b c K φ α hgate hsz => by
        rw [← Formula.size_transpose] at hgate
        rw [← Formula.size_transpose] at hsz
        simp only [Formula.transpose] at hsz ⊢
        exact Pf.axKf a b c K φ.transpose α.transpose hgate hsz)
    -- box4
    (fun a b K φ hgate hsz => by
        rw [← Formula.size_transpose] at hgate
        rw [← Formula.size_transpose] at hsz
        simp only [Formula.transpose] at hgate hsz ⊢
        exact Pf.box4 a b K φ.transpose hgate hsz)
    -- boxMono
    (fun a b K φ hab hsz => by
        rw [← Formula.size_transpose] at hsz
        simp only [Formula.transpose] at hsz ⊢
        exact Pf.boxMono a b K φ.transpose hab hsz)
    -- diagF: the Löb fixpoint is C/D-blind — `(.diag g tgt)^τ = .diag g tgt^τ`
    (fun pm fb g K tgt _ hle ih => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ih ⊢
        exact Pf.diagF pm fb g K tgt.transpose ih hle)
    -- diagB
    (fun pm fb g K tgt _ hle ih => by
        rw [← Formula.size_transpose] at hle
        simp only [Formula.transpose] at hle ih ⊢
        exact Pf.diagB pm fb g K tgt.transpose ih hle)
    -- searchElseChain
    (fun hd L a me opponent hme hle => by
        subst hme
        rw [← Formula.size_transpose] at hle
        rw [← layersCost_transpose (hd :: L)] at hle
        simp only [Formula.transpose, Prog.transpose,
          plug2_transpose, guard2_transpose, guards2_transpose,
          implChain_transpose, List.map_cons] at hle ⊢
        exact Pf.searchElseChain hd.transpose (L.map SearchLayer2.transpose) a.swap
          _ opponent.transpose rfl hle)
    h

/-- Theorem 1.10 as the biconditional (`τ` is an involution, so invariance is
    an equivalence — the paper's `⊢_k φ ⟺ ⊢_k φ^τ`). -/
theorem Pf.transpose_iff (k : Nat) (φ : Formula) : Pf k φ ↔ Pf k φ.transpose :=
  ⟨Pf.transpose, fun h => by simpa using Pf.transpose h⟩

end PD
