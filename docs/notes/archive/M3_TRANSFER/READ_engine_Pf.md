# Engine proof system — verbatim extraction (read-only audit, branch `colomban-arith-s`)

All paths relative to `engine/PrisonersDilemma/`. Line numbers from the current tree. Nothing was built.

**Headline counts / ranges**
- `Prog`: 10 constructors (`Program.lean:26–69`); `ProgList` 2 (`:74–76`); `VoteList` 2 (`:81–83`); `Formula`: 6 constructors (`:84–90`).
- Mutual proof block `ProofSystem.lean:157–531`: `PlaysProof` 15 constructors (`:161–261`), `VoteAllPlay` 2 (`:266–269`), `AtomProvable` 1 (`:273–274`), **`Pf` 33 constructors (`:287–531`)**: 15 Family A (reading), 9 Family B (glue), 8 Family C (Löb) + `searchElseChain` (declared last, at `:523–530`, semantically Family A). (The header comment "Pf arms (27…)" at `:718` and "PlaysProof arms (19)" at `:706` are stale.)
- `Pf.induct` `:541–760`; `PlaysProof.induct` `:766–883`; `atom_monotone` `:890`; `Pf_mono` `:894–957`; `proofSearch` `:961`; `atom_cost` `:967`.
- `Formula.diag` is a **constructor** of `Formula` (`Program.lean:90`), not a defined helper; `diagF`/`diagB` use `.diag g tgt` directly. No other `Formula`-level helper is involved.

---

## (1) Syntax — `Program.lean`

### `Action`, `Outcome` (`:3–8`)
```lean
inductive Action
  | C
  | D
  deriving DecidableEq, Repr, BEq

abbrev Outcome := Action × Action
```

### The mutual block `Prog`/`ProgList`/`VoteList`/`Formula` (`:25–92`, comments stripped where they are pure prose; argument types verbatim)
```lean
mutual
  inductive Prog: Type where
    | const  : Action → Prog
    | self   : Prog
    | opp    : Prog
    | bot    : Prog → Prog                        -- closed bot reference; `subst` does not descend
    | sim    : Prog → Prog → Prog
    | ite    : Prog → Action → Prog → Prog → Prog -- if evaluating guard yields action a, run p, else q
    | search : Nat → Formula → Prog → Prog → Prog -- proof_search(k, φ): if oracle verifies φ in ≤k chars, run p, else q
    | tvote : VoteList → Nat → Prog → Prog → Prog
        -- `tvote v θ p q` peels the weighted entries `v` IN LIST ORDER; an entry
        -- `(w, I)` fires iff the closed program `I` PLAYS `C` (running against itself —
        -- entries are `.opp`-free instances), and firing subtracts `w` from the residual
        -- threshold (truncated). Residual 0 → run `p`; entries exhausted with residual
        -- > 0 → run `q`.   ... NO budget argument: the vote itself never consults the oracle.
        -- Entries are FROZEN (like `.bot` / the `.eq` RHS / `.diag`): `subst` does not
        -- descend into a `VoteList`.
    | sys     : ProgList → Nat → Prog
        -- the MUTUAL-FIXPOINT BINDER ... `sys defs i` is the i-th component of the
        -- mutually-recursive system `defs`, whose members refer to each other via
        -- `.selfIdx`. LAZY unfold: `eval` closes one level per fuel tick via
        -- `sysClose` (never at definition time). Out-of-range `i` evals to `none`.
        -- `.sys` is a BINDER: neither `subst` nor an outer `sysClose` descends into `defs`.
    | selfIdx : Nat → Prog
        -- reference to system component `j` — closed by `sysClose`, NEVER by `subst`.
        -- A bare `.selfIdx` outside any system is a dangling reference and evals to `none`.
  inductive ProgList : Type where
    | nil  : ProgList
    | cons : Prog → ProgList → ProgList
  inductive VoteList : Type where
    | nil  : VoteList
    | cons : Nat → Prog → VoteList → VoteList
  inductive Formula: Type where
    | plays : Prog → Prog → Action → Formula      -- atomic: "p(q.source) == a"
    | impl  : Formula → Formula → Formula
    | neg   : Formula → Formula
    | box   : Nat → Formula → Formula             -- □_n φ: "S derives φ at budget n" (⊢_n φ; its interp is `Pf n φ`)
    | eq    : Prog → Prog → Formula               -- structural identity. The 2nd arg is a frozen literal target (subst does not descend into it); the 1st is the probe (typically `.opp`)
    | diag  : Nat → Formula → Formula             -- the Löb-fixpoint sentence for target `tgt` at box budget `g`: ψ with ψ ↔ (□_g ψ → tgt). ... Never appears in bot source; used only by the meta Löb chain
end
deriving instance DecidableEq for Prog, VoteList, ProgList, Formula
```

### `subst` (`:126–152`)
```lean
mutual
  def Prog.subst : Prog → (me opponent : Prog) → Prog
    | .const a,        _, _ => .const a
    | .self,           m, _ => m
    | .opp,            _, o => o
    | .bot p,          _, _ => .bot p
    | .sim p q,        m, o => .sim (p.subst m o) (q.subst m o)
    | .ite b a p q,    m, o => .ite (b.subst m o) a (p.subst m o) (q.subst m o)
    | .search k φ p q, m, o => .search k (φ.subst m o) (p.subst m o) (q.subst m o)
    | .tvote v θ p q,      m, o => .tvote v θ (p.subst m o) (q.subst m o)
    | .sys defs i,     _, _ => .sys defs i
    | .selfIdx j,      _, _ => .selfIdx j
  termination_by structural p _ _ => p

  def Formula.subst : Formula → (me opponent : Prog) → Formula
    | .plays p q a, m, o => .plays (p.subst m o) (q.subst m o) a
    | .impl φ ψ,    m, o => .impl (φ.subst m o) (ψ.subst m o)
    | .neg φ,       m, o => .neg (φ.subst m o)
    | .box n φ,     m, o => .box n (φ.subst m o)
    | .eq p q,      m, o => .eq (p.subst m o) q   -- only the LHS (probe) substitutes; the RHS is a frozen literal target
    | .diag g φ,    _, _ => .diag g φ             -- FROZEN
  termination_by structural f _ _ => f
end
```
Note: `subst` is one-shot (not a fixed point); placeholders inside the inserted `me`/`opponent` are not re-substituted (`:111–113`).

### `sysClose` (`:169–197`) and `ProgList.get?` (`:201–204`)
```lean
mutual
  def Prog.sysClose (defs : ProgList) : Prog → Prog
    | .const a            => .const a
    | .self               => .self
    | .opp                => .opp
    | .bot p              => .bot (p.sysClose defs)
    | .sim p q            => .sim (p.sysClose defs) (q.sysClose defs)
    | .ite b a p q        => .ite (b.sysClose defs) a (p.sysClose defs) (q.sysClose defs)
    | .search k φ p q     => .search k (φ.sysClose defs) (p.sysClose defs) (q.sysClose defs)
    | .tvote v θ p q      => .tvote v θ (p.sysClose defs) (q.sysClose defs)   -- entries FROZEN
    | .sys dl i           => .sys dl i            -- inner system: BINDER (shadowing)
    | .selfIdx j          => .sys defs j          -- the closer itself
  termination_by structural p => p

  def Formula.sysClose (defs : ProgList) : Formula → Formula
    | .plays p q a => .plays (p.sysClose defs) (q.sysClose defs) a
    | .impl φ ψ    => .impl (φ.sysClose defs) (ψ.sysClose defs)
    | .neg φ       => .neg (φ.sysClose defs)
    | .box n φ     => .box n (φ.sysClose defs)
    | .eq p q      => .eq (p.sysClose defs) (q.sysClose defs)   -- BOTH sides (unlike subst)
    | .diag g φ    => .diag g (φ.sysClose defs)                  -- descends (unlike subst)
  termination_by structural f => f
end

def ProgList.get? : ProgList → Nat → Option Prog
  | .nil,         _     => none
  | .cons p _,    0     => some p
  | .cons _ rest, n + 1 => rest.get? n
```

### `size` (`:215–253`)
```lean
def numCost (k : Nat) : Nat := Nat.log2 k + 1

mutual
  def Prog.size : Prog → Nat
    | .const _        => 1
    | .self           => 1
    | .opp            => 1
    | .bot p          => p.size + 1
    | .sim p q        => p.size + q.size + 1
    | .ite b _ p q    => b.size + p.size + q.size + 1
    | .search k φ p q => numCost k + φ.size + p.size + q.size + 1
    | .tvote v θ p q      => numCost θ + v.vsize + p.size + q.size + 1
    | .sys defs i     => defs.psize + numCost i + 1
    | .selfIdx j      => numCost j + 1

  def VoteList.vsize : VoteList → Nat
    | .nil           => 0
    | .cons w I rest => numCost w + I.size + rest.vsize + 1

  def ProgList.psize : ProgList → Nat
    | .nil         => 0
    | .cons p rest => p.size + rest.psize + 1

  def Formula.size : Formula → Nat
    | .plays p q _ => p.size + q.size + 1
    | .impl φ ψ    => φ.size + ψ.size + 1
    | .neg φ       => φ.size + 1
    | .box k φ     => numCost k + φ.size + 1
    | .eq p q      => p.size + q.size + 1
    | .diag g φ    => numCost g + φ.size + 1
end
```

### Other `Program.lean` helpers used by the proof system (`:259–293`)
```lean
def Prog.hasSearch : Prog → Bool
  | .const _        => false
  | .self           => false
  | .opp            => false
  | .bot p          => p.hasSearch
  | .sim p q        => p.hasSearch || q.hasSearch
  | .ite b _ p q    => b.hasSearch || p.hasSearch || q.hasSearch
  | .search _ _ _ _ => true
  | .tvote _ _ _ _     => true   -- UNCONDITIONALLY true (conservative)
  | .sys _ _        => true      -- CONSERVATIVE
  | .selfIdx _      => true

def VoteList.totalMass : VoteList → Nat
  | .nil           => 0
  | .cons w _ rest => w + rest.totalMass

def VoteList.massWhere (f : Prog → Bool) : VoteList → Nat
  | .nil           => 0
  | .cons w I rest => (if f I then w else 0) + rest.massWhere f
```

---

## (2) Dynamics — `Dynamics.lean`

### `eval` (`:20–76`) — verbatim, every clause
```lean
noncomputable def eval : Nat → (me opponent body : Prog) → Option Action
  | 0,   _,  _,   _    => none
  | n+1, me, opponent, body => match body with
    | .const a        => some a
    | .self           => eval n me opponent me
    | .opp            => eval n me opponent opponent
    | .bot p          => eval n me opponent p
    | .sim p q        =>
        let p' := p.subst me opponent
        let q' := q.subst me opponent
        eval n p' q' p'
    | .ite b a p q    => do
        let r ← eval n me opponent b
        if r == a then eval n me opponent p else eval n me opponent q
    | .search k φ p q =>
        if proofSearch k (φ.subst me opponent)
          then eval n me opponent p
          else eval n me opponent q
    | .tvote .nil θ p q =>
        if θ = 0 then eval n me opponent p else eval n me opponent q
    | .tvote (.cons w I rest) θ p q =>
        if θ = 0 then eval n me opponent p
        else match eval n (.bot I) (.bot I) I with
          | some Action.C => eval n me opponent (.tvote rest (θ - w) p q)
          | some Action.D => eval n me opponent (.tvote rest θ p q)
          | none          => none
    | .sys defs i =>
        match defs.get? i with
        | some p => eval n me opponent (p.sysClose defs)
        | none   => none
    | .selfIdx _ => none
```
`noncomputable` solely because `proofSearch` is classical. Unfolding lemmas: `eval_tvote_zero/nil/cons_c/cons_d/cons_none` (`:84–118`), `eval_sys_some/none`, `eval_selfIdx` (`:126–138`).

### `proofSearch` (`ProofSystem.lean:961`), `play`, `outcome` (`Dynamics.lean:140–146`)
```lean
noncomputable def proofSearch (k : Nat) (φ : Formula) : Bool := decide (Pf k φ)

noncomputable def play (fuel : Nat) (me opponent : Prog) : Option Action :=
  eval fuel me opponent me

noncomputable def outcome (fuel : Nat) (p q : Prog) : Option Outcome := do
  let a ← play fuel p q
  let b ← play fuel q p
  some (a, b)
```

### `Formula.interp` (`Dynamics.lean:152–158`)
```lean
def Formula.interp : Formula → Prop
  | .plays p q a => ∃ n, play n p q = some a
  | .impl φ ψ    => φ.interp → ψ.interp
  | .neg φ       => ¬ φ.interp
  | .box n φ     => Pf n φ
  | .eq p q      => p = q
  | .diag g φ    => Pf g (.diag g φ) → φ.interp
```
So **yes: `(.box n φ).interp = Pf n φ` definitionally**, `.plays` is fuel-existential, `.eq` is Lean structural equality of `Prog`, `.diag g φ` is the fixpoint `□_g(diag g φ) → φ` by definition.

---

## (3) The mutual block — `ProofSystem.lean:157–531`

### Cost constants and telescope helpers (`:70–155`)
```lean
def c_leaf  : Nat := 1
def c_node  : Nat := 1
def c_guard (k : Nat) : Nat := numCost k

def searchPlug : List (Nat × Formula × Prog) → Prog → Prog
  | [], p => p
  | (g, ψ, e) :: L, p => .search g ψ (searchPlug L p) e
def searchGuards (me opponent : Prog) : List (Nat × Formula × Prog) → List Formula
  | [] => []
  | (g, ψ, _) :: L => .box g (ψ.subst me opponent) :: searchGuards me opponent L
def implChain (gs : List Formula) (tgt : Formula) : Formula :=
  gs.foldr .impl tgt

inductive CtxLayer where
  | searchL (g : Nat) (ψ : Formula) (e : Prog)
  | iteL (z : Prog) (aT : Action) (other : Prog)
def ctxPlug : List CtxLayer → Prog → Prog
  | [], p => p
  | .searchL g ψ e :: L, p => .search g ψ (ctxPlug L p) e
  | .iteL z aT other :: L, p => .ite (.sim .opp (.bot z)) aT (ctxPlug L p) other
def ctxGuard (me opponent : Prog) : CtxLayer → Formula
  | .searchL g ψ _ => .box g (ψ.subst me opponent)
  | .iteL z aT _ => .plays opponent (.bot z) aT
def ctxGuards (me opponent : Prog) : List CtxLayer → List Formula
  | [] => []
  | hd :: L => ctxGuard me opponent hd :: ctxGuards me opponent L

inductive SearchLayer2 where
  | thenL (g : Nat) (ψ : Formula) (e : Prog)
  | elseL (g : Nat) (P Q : Prog) (c : Action) (p : Prog)
def plug2 : List SearchLayer2 → Prog → Prog
  | [], p => p
  | .thenL g ψ e :: L, p => .search g ψ (plug2 L p) e
  | .elseL g P Q c q :: L, p => .search g (.plays P Q c) q (plug2 L p)
def guard2 (me opponent : Prog) : SearchLayer2 → Formula
  | .thenL g ψ _ => .box g (ψ.subst me opponent)
  | .elseL _ P Q c _ => .neg (.plays (P.subst me opponent) (Q.subst me opponent) c)
def guards2 (me opponent : Prog) : List SearchLayer2 → List Formula
  | [] => []
  | hd :: L => guard2 me opponent hd :: guards2 me opponent L
def layerCost : SearchLayer2 → Nat
  | .thenL g _ _ => c_guard g
  | .elseL g _ _ _ _ => g + c_node
def layersCost : List SearchLayer2 → Nat
  | [] => 0
  | hd :: L => layerCost hd + layersCost L
```
`atom_cost` (`:967`): `def atom_cost (fuel : Nat) : Nat := c_leaf + (c_node + c_guard fuel) * fuel`.

### 3a. `PlaysProof` — evaluation certificates (`:161–261`)
Signature: `inductive PlaysProof : (me opponent body : Prog) → Action → Nat → Prop`. Recursive premises are `PlaysProof` unless marked `Pf`. Side facts marked **[Lean]**.
```lean
    | const :
        PlaysProof me opponent (.const a) a c_leaf
    | self :
        PlaysProof me opponent me a n →
        PlaysProof me opponent .self a (n + c_node)
    | opp :
        PlaysProof me opponent opponent a n →
        PlaysProof me opponent .opp a (n + c_node)
    | bot :
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.bot p) a (n + c_node)
    | sim :
        PlaysProof (p.subst me opponent) (q.subst me opponent) (p.subst me opponent) a n →
        PlaysProof me opponent (.sim p q) a (n + c_node)
    | ite_t :
        PlaysProof me opponent b r m → (r == a') = true →          -- [Lean: Bool eq]
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.ite b a' p q) a (m + n + c_node)
    | ite_f :
        PlaysProof me opponent b r m → (r == a') = false →         -- [Lean]
        PlaysProof me opponent q a n →
        PlaysProof me opponent (.ite b a' p q) a (m + n + c_node)
    | search_t :
        Pf k (φ.subst me opponent) →                                -- RECURSIVE Pf (the back-edge)
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.search k φ p q) a (n + c_guard k + c_node)
    | search_f :
        Pf m (.neg (φ.subst me opponent)) →                         -- RECURSIVE Pf: Σ₁ REFUTATION, budget m free
        PlaysProof me opponent q a n →
        PlaysProof me opponent (.search k φ p q) a (n + m + k + c_node)   -- pays FULL failed budget k (the floor)
    | voteZero_t {me opponent p q : Prog} {a : Action} {n : Nat} {v : VoteList} :
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.tvote v 0 p q) a (n + c_node)
    | voteNil_f {me opponent p q : Prog} {a : Action} {n θ : Nat} :
        θ ≠ 0 →                                                     -- [Lean]
        PlaysProof me opponent q a n →
        PlaysProof me opponent (.tvote .nil θ p q) a (n + c_node)
    | voteCons_c {me opponent p q : Prog} {a : Action} {n θ w m : Nat} {I : Prog}
        {rest : VoteList} :
        θ ≠ 0 →                                                     -- [Lean]
        PlaysProof (.bot I) (.bot I) I Action.C m →
        PlaysProof me opponent (.tvote rest (θ - w) p q) a n →
        PlaysProof me opponent (.tvote (.cons w I rest) θ p q) a (n + m + c_node)
    | voteCons_d {me opponent p q : Prog} {a : Action} {n θ w m : Nat} {I : Prog}
        {rest : VoteList} :
        θ ≠ 0 →                                                     -- [Lean]
        PlaysProof (.bot I) (.bot I) I Action.D m →
        PlaysProof me opponent (.tvote rest θ p q) a n →
        PlaysProof me opponent (.tvote (.cons w I rest) θ p q) a (n + m + c_node)
    | voteHigh_f {me opponent p q : Prog} {a : Action} {n θ : Nat} {v : VoteList} :
        θ > v.totalMass →                                           -- [Lean]
        VoteAllPlay v c →                                           -- RECURSIVE (VoteAllPlay, below)
        PlaysProof me opponent q a n →
        PlaysProof me opponent (.tvote v θ p q) a (n + c + v.vsize + c_node)
    | sysStep {me opponent : Prog} {defs : ProgList} {i : Nat} {p : Prog} {a : Action}
        {n : Nat} :
        defs.get? i = some p →                                      -- [Lean: decidable list lookup]
        PlaysProof me opponent (p.sysClose defs) a n →
        PlaysProof me opponent (.sys defs i) a (n + c_node)
```
No rule for `.selfIdx` (`:253–256`: "nothing about it should be `S`-derivable"). The `.tvote` block has **no floor and no `Pf` premise** (`:209–216`).

```lean
  inductive VoteAllPlay : VoteList → Nat → Prop where
    | nil : VoteAllPlay .nil 0
    | cons {w : Nat} {I : Prog} {rest : VoteList} {a : Action} {m c : Nat} :
        PlaysProof (.bot I) (.bot I) I a m → VoteAllPlay rest c → VoteAllPlay (.cons w I rest) (m + c)

  inductive AtomProvable : Nat → Formula → Prop where
    | mk : PlaysProof me opponent me a n → n ≤ k → AtomProvable k (.plays me opponent a)
```
(`AtomProvable` only ever holds at a `.plays` with body = `me`; `n ≤ k` is [Lean].)

### 3b. `Pf : Nat → Formula → Prop` (`:287–531`) — every constructor verbatim

**Group: execution bridge / refutation suppliers**
```lean
    | atom : AtomProvable k φ → Pf k φ                                          -- :291  recursive: AtomProvable
    | atomNeg (p q : Prog) (b aN : Action) (m : Nat) :                          -- :295–298
        AtomProvable m (.plays p q b) → b ≠ aN →                                -- AtomProvable; [Lean: b ≠ aN]
        m + (Formula.neg (.plays p q aN)).size ≤ k →                            -- [Lean]
        Pf k (.neg (.plays p q aN))
    | eqRefl (p : Prog) :                                                       -- :413–414
        (Formula.eq p p).size ≤ k → Pf k (.eq p p)                              -- [Lean] only
    | eqNeg (p q : Prog) (hne : p ≠ q) :                                        -- :417–418
        (Formula.neg (.eq p q)).size ≤ k → Pf k (.neg (.eq p q))                -- [Lean: p ≠ q, size]
```

**Group: search-polarity / source-transparency reading rules (Family A2)** — all premise-free except where a `Pf` premise is marked; `hme : me = …` is a [Lean] definitional-equality side fact.
```lean
    | searchBranch (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)   -- :302–305
        (hme : me = .search g ψ (.const a) (.const b)) :
        (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
    | simStep (me p q opponent : Prog) (a : Action) (hme : me = .sim p q) :      -- :307–311
        (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                      (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                    (.plays me opponent a))
    | botSimStep (me p q opponent : Prog) (a : Action) (hme : me = .bot (.sim p q)) :   -- :315–319
        (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                      (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                    (.plays me opponent a))
    | botSearchStep (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)  -- :322–325
        (hme : me = .bot (.search g ψ (.const a) (.const b))) :
        (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
    | botSysSearchStep (defs : ProgList) (i : Nat) (g : Nat) (ψ : Formula)     -- :331–338
        (a b : Action) (me opponent : Prog)
        (hme : me = .bot (.sys defs i))
        (hget : defs.get? i = some (.search g ψ (.const a) (.const b))) :
        (Formula.impl (.box g ((ψ.sysClose defs).subst me opponent))
                      (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.box g ((ψ.sysClose defs).subst me opponent))
                    (.plays me opponent a))
    | botSysSimStep (defs : ProgList) (i j : Nat) (a : Action) (me opponent : Prog)   -- :344–350
        (hme : me = .bot (.sys defs i))
        (hget : defs.get? i = some (.sim (.bot (.selfIdx j)) (.bot (.selfIdx j)))) :
        (Formula.impl (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) a)
                      (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) a)
                    (.plays me opponent a))
    | botSysSearchThenSearch (defs : ProgList) (i k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula)   -- :354–362
        (c0 c1 : Action) (q me opponent : Prog)
        (hme : me = .bot (.sys defs i))
        (hget : defs.get? i = some (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q)) :
        Pf m ((ψ₂.sysClose defs).subst me opponent) → m ≤ k₂ →                 -- RECURSIVE Pf; [Lean m ≤ k₂]
        c_guard k₂ +
          (Formula.impl (.box k₁ ((ψ₁.sysClose defs).subst me opponent))
            (.plays me opponent c0)).size ≤ k →
        Pf k (.impl (.box k₁ ((ψ₁.sysClose defs).subst me opponent)) (.plays me opponent c0))
    | iteBranchSearch_t (g : Nat) (z : Prog) (a' c0 c1 : Action) (ψ : Formula)   -- :369–378
        (q me opponent : Prog)
        (hme : me = .ite (.sim .opp (.bot z)) a'
                         (.search g ψ (.const c0) (.const c1)) q) :
        (Formula.impl (.plays opponent (.bot z) a')
                      (.impl (.box g (ψ.subst me opponent))
                             (.plays me opponent c0))).size ≤ k →
        Pf k (.impl (.plays opponent (.bot z) a')
                    (.impl (.box g (ψ.subst me opponent))
                           (.plays me opponent c0)))
    | searchThenSearch_t (k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula) (c0 c1 : Action)    -- :383–389
        (q me opponent : Prog)
        (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) :
        Pf m (ψ₂.subst me opponent) → m ≤ k₂ →                                  -- RECURSIVE Pf; [Lean]
        c_guard k₂ +
          (Formula.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0)).size ≤ k →
        Pf k (.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0))
    | searchChain (g₁ : Nat) (ψ₁ : Formula) (e₁ : Prog)                          -- :395–401
        (L : List (Nat × Formula × Prog)) (a : Action) (me opponent : Prog)
        (hme : me = .search g₁ ψ₁ (searchPlug L (.const a)) e₁) :
        (Formula.impl (.box g₁ (ψ₁.subst me opponent))
          (implChain (searchGuards me opponent L) (.plays me opponent a))).size ≤ k →
        Pf k (.impl (.box g₁ (ψ₁.subst me opponent))
          (implChain (searchGuards me opponent L) (.plays me opponent a)))
    | ctxChain (hd : CtxLayer) (L : List CtxLayer) (a : Action) (me opponent : Prog)   -- :406–411
        (hme : me = ctxPlug (hd :: L) (.const a)) :
        (Formula.impl (ctxGuard me opponent hd)
          (implChain (ctxGuards me opponent L) (.plays me opponent a))).size ≤ k →
        Pf k (.impl (ctxGuard me opponent hd)
          (implChain (ctxGuards me opponent L) (.plays me opponent a)))
    | searchElseChain (hd : SearchLayer2) (L : List SearchLayer2) (a : Action)   -- :523–530
        (me opponent : Prog)
        (hme : me = plug2 (hd :: L) (.const a)) :
        layersCost (hd :: L) +
          (Formula.impl (guard2 me opponent hd)
            (implChain (guards2 me opponent L) (.plays me opponent a))).size ≤ k →
        Pf k (.impl (guard2 me opponent hd)
          (implChain (guards2 me opponent L) (.plays me opponent a)))
```
Note: `search_t`/`search_f` are `PlaysProof` constructors (above), not `Pf` constructors. There is **no** `.tvote`- or `.sys`-reading rule in `Pf` beyond the three `botSys*` rules; the tau vote enters `S` only through `PlaysProof` (evaluation certificates) — "tau rules" in `Pf` = `botSysSearchStep`, `botSysSimStep`, `botSysSearchThenSearch` (all require `me = .bot (.sys defs i)`).

**Group: propositional glue (Family B)** — recursive premises are `Pf`; the `≤ k`/`≤ K` line is [Lean].
```lean
    | mp (m₁ m₂ : Nat) (φ α : Formula) :                                        -- :422–423
        Pf m₁ (.impl φ α) → Pf m₂ φ → m₁ + m₂ + α.size ≤ k → Pf k α
    | implTrans (φ ψ χ : Formula) (a b : Nat) :                                  -- :426–428
        Pf a (.impl φ ψ) → Pf b (.impl ψ χ) →
        a + b + (Formula.impl φ χ).size ≤ k → Pf k (.impl φ χ)
    | weakenImpl (φ ψ : Formula) (m : Nat) :                                     -- :432–433
        Pf m ψ → m + (Formula.impl φ ψ).size ≤ k → Pf k (.impl φ ψ)
    | impS2 (φ ψ χ : Formula) (m₁ m₂ K : Nat) :                                  -- :436–438
        Pf m₁ (.impl φ (.impl ψ χ)) → Pf m₂ (.impl φ ψ) →
        m₁ + m₂ + (Formula.impl φ χ).size ≤ K → Pf K (.impl φ χ)
    | implRefl (φ : Formula) :                                                   -- :441–442
        (Formula.impl φ φ).size ≤ k → Pf k (.impl φ φ)
    | implK (φ ψ : Formula) :                                                    -- :444–445
        (Formula.impl φ (.impl ψ φ)).size ≤ k → Pf k (.impl φ (.impl ψ φ))
    | implS (φ ψ χ : Formula) :                                                  -- :449–452
        (Formula.impl (.impl φ (.impl ψ χ))
          (.impl (.impl φ ψ) (.impl φ χ))).size ≤ k →
        Pf k (.impl (.impl φ (.impl ψ χ)) (.impl (.impl φ ψ) (.impl φ χ)))
    | contrapose (φ ψ : Formula) (m : Nat) :                                     -- :454–457
        Pf m (.impl φ ψ) →
        m + (Formula.impl (.neg ψ) (.neg φ)).size ≤ k →
        Pf k (.impl (.neg ψ) (.neg φ))
    | negElim (φ ψ : Formula) (m₁ m₂ : Nat) :                                    -- :461–464
        Pf m₁ (.neg φ) → Pf m₂ φ →
        m₁ + m₂ + ψ.size ≤ k →
        Pf k ψ
```
No implication introduction / deduction theorem as a rule (`:39–42`); it is ADMISSIBLE (`Base/Closure.deduction_theorem`, per `:446–448`).

**Group: modal / Löb machinery (Family C)**
```lean
    | boxIntro (kIn K : Nat) (φ : Formula) :                                     -- :469–472
        Pf kIn φ →                                                              -- RECURSIVE
        kIn + (Formula.box kIn φ).size ≤ K →
        Pf K (.box kIn φ)
    | atomBoxImpl (kBox : Nat) (p q : Prog) (a : Action) :                       -- :476–479
        AtomProvable kBox (.plays p q a) →                                      -- recursive AtomProvable
        kBox + (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ k →
        Pf k (.impl (.plays p q a) (.box kBox (.plays p q a)))
    | axK (a b c m K : Nat) (φ α : Formula) :                                    -- :481–485
        Pf m (.box a (.impl φ α)) →                                             -- RECURSIVE
        a + b + α.size ≤ c →                                                    -- [Lean] the K gate
        m + (Formula.impl (.box b φ) (.box c α)).size ≤ K →
        Pf K (.impl (.box b φ) (.box c α))
    | axKf (a b c K : Nat) (φ α : Formula) :                                     -- :487–490 (premise-free)
        a + b + α.size ≤ c →
        (Formula.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))).size ≤ K →
        Pf K (.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α)))
    | box4 (a b K : Nat) (φ : Formula) :                                         -- :493–496 (premise-free)
        a + (Formula.box a φ).size ≤ b →
        (Formula.impl (.box a φ) (.box b (.box a φ))).size ≤ K →
        Pf K (.impl (.box a φ) (.box b (.box a φ)))
    | boxMono (a b K : Nat) (φ : Formula) :                                      -- :500–503 (premise-free)
        a ≤ b →
        (Formula.impl (.box a φ) (.box b φ)).size ≤ K →
        Pf K (.impl (.box a φ) (.box b φ))
    | diagF (pm fb g K : Nat) (tgt : Formula) :                                  -- :508–511
        Pf pm (.impl (.box fb tgt) tgt) →                                       -- RECURSIVE: the Löb-premise GATE
        pm + (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K →
        Pf K (.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt))
    | diagB (pm fb g K : Nat) (tgt : Formula) :                                  -- :513–516
        Pf pm (.impl (.box fb tgt) tgt) →                                       -- RECURSIVE gate
        pm + (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K →
        Pf K (.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt))
```
Note the `fb` in `diagF`/`diagB` is unconstrained relative to `g` — the gate only requires SOME Löb premise at some subscript `fb` to be held.

**Which premises are recursive vs Lean side facts (summary table)**

| Constructor | Recursive premises | Lean side facts |
|---|---|---|
| `atom` | `AtomProvable k φ` | — |
| `atomNeg` | `AtomProvable m (.plays p q b)` | `b ≠ aN`, `m + |¬plays p q aN| ≤ k` |
| `searchBranch`,`simStep`,`botSimStep`,`botSearchStep`,`iteBranchSearch_t`,`searchChain`,`ctxChain`,`searchElseChain` | none | `hme : me = <shape>`, `size ≤ k` (+`layersCost` for `searchElseChain`) |
| `botSysSearchStep`,`botSysSimStep` | none | `hme`, `hget : defs.get? i = some …`, size |
| `botSysSearchThenSearch`,`searchThenSearch_t` | `Pf m (inner guard)` | `hme`,(`hget`), `m ≤ k₂`, `c_guard k₂ + size ≤ k` |
| `eqRefl` / `eqNeg` | none | size; `p ≠ q` |
| `mp`,`implTrans`,`impS2`,`negElim` | two `Pf` | sum-cost `≤ k/K` |
| `weakenImpl`,`contrapose`,`boxIntro`,`axK`,`diagF`,`diagB` | one `Pf` | cost (+`a+b+|α| ≤ c` for `axK`) |
| `atomBoxImpl` | `AtomProvable kBox` | cost |
| `implRefl`,`implK`,`implS`,`axKf`,`box4`,`boxMono` | none | size / gate inequalities |

### Eliminators / monotonicity (`:541–957`)
```lean
@[elab_as_elim]
theorem Pf.induct (motive : (k : Nat) → (φ : Formula) → Pf k φ → Prop)
    (atom : ∀ (k : Nat) (φ : Formula) (h : AtomProvable k φ), motive k φ (.atom h))
    … (one named hypothesis per constructor, IHs only on `Pf` premises; see :542–699) …
    {k : Nat} {φ : Formula} (h : Pf k φ) : motive k φ h
```
Implemented by raw `Pf.rec` with `motive_1/2/3 := True` (PlaysProof, VoteAllPlay, AtomProvable) and `motive_4 := motive` (`:701–760`). `PlaysProof.induct` (`:766–883`) has motive `(me opponent body : Prog) → (a : Action) → (n : Nat) → PlaysProof me opponent body a n → Prop`; the `Pf` premises of `search_t`/`search_f` are handed over as DATA without IH (`:762–765`).
```lean
theorem atom_monotone (k₁ k₂ : Nat) (φ : Formula) (hk : k₁ ≤ k₂) :
    AtomProvable k₁ φ → AtomProvable k₂ φ                                          -- :890
theorem Pf_mono : ∀ {k₁ : Nat} {φ : Formula}, Pf k₁ φ →
    ∀ {k₂ : Nat}, k₁ ≤ k₂ → Pf k₂ φ                                                -- :894  (plain `cases`, no recursion)
```

---

## (4) Soundness — `Base/Soundness.lean`, `Base/ValuationSoundness.lean`

`(.box n φ).interp = Pf n φ` is definitional (Dynamics `:156`); inside soundness `WV S (.box n φ) = Pf n φ` also (`ValuationSoundness.lean:372`, `WV_box :383` by `rfl`). So the box arm of soundness is the identity — `boxIntro`'s soundness is `Pf kIn φ → Pf kIn φ`; `box4`'s interp is `Pf a φ → Pf a φ`.

```lean
-- Base/Soundness.lean:103–106
theorem sound_upto : ∀ B : Nat,
    (∀ me opponent body a n, PlaysProof me opponent body a n → n ≤ B →
      ∃ N, eval N me opponent body = some a)
    ∧ (∀ k φ, Pf k φ → k ≤ B → φ.interp)

theorem playsProof_sound {me opponent body a n} (h : PlaysProof me opponent body a n) :
    ∃ N, eval N me opponent body = some a                                            -- :128
theorem AtomProvable_sound (k : Nat) (φ : Formula) : AtomProvable k φ → φ.interp     -- :134
theorem Pf_sound : ∀ k φ, Pf k φ → φ.interp                                          -- :143
theorem proofSearch_sound : ∀ k φ, proofSearch k φ = true → φ.interp                 -- :179
theorem proofSearch_complete_plays :
    ∀ p q a, p.hasSearch = false → q.hasSearch = false →
      (∃ n, play n p q = some a) → ∃ k, proofSearch k (.plays p q a) = true          -- :186
theorem proofSearch_monotone :
    ∀ k₁ k₂ φ, k₁ ≤ k₂ → proofSearch k₁ φ = true → proofSearch k₂ φ = true            -- :195
theorem box_provable (k : Nat) (φ : Formula) (h : Pf k φ) :
    ∃ K, K ≤ k + (Formula.box k φ).size ∧ Pf K (.box k φ)                             -- :207
theorem atom_box_provable_impl_sound (k K : Nat) (p q : Prog) (a : Action)
    (hatom : AtomProvable k (.plays p q a))
    (hK : k + (Formula.box k (.plays p q a)).size
          + (Formula.impl (.plays p q a) (.box k (.plays p q a))).size ≤ K) :
    Pf K (.impl (.plays p q a) (.box k (.plays p q a)))                              -- :220
-- Base/AtomCerts.lean
theorem proofSearch_spec (k : Nat) (φ : Formula) : proofSearch k φ = true ↔ Pf k φ    -- :187
theorem atom_complete_searchfree (p q : Prog) (a : Action) (fuel : Nat)
    (hp : p.hasSearch = false) (hq : q.hasSearch = false)
    (h : play fuel p q = some a) : AtomProvable (3 ^ fuel) (.plays p q a)             -- :138
theorem atom_search_t_top (k : Nat) (g : Formula) (aT aE : Action) (oppo : Prog)
    (hg : Pf k (g.subst (.search k g (.const aT) (.const aE)) oppo)) :
    AtomProvable (Nat.log2 k + 3) (.plays (.search k g (.const aT) (.const aE)) oppo aT)   -- :146
theorem atom_search_f_top (k m : Nat) (g : Formula) (aT aE : Action) (oppo : Prog)
    (hneg : Pf m (.neg (g.subst (.search k g (.const aT) (.const aE)) oppo))) :
    AtomProvable (m + k + 2) (.plays (.search k g (.const aT) (.const aE)) oppo aE)        -- :167  (the floor ≥ k+1)
```
`sound_upto` is proved by instantiating the master at `S = S' = fun _ _ => False` (`Soundness.lean:108–124`). The master (`ValuationSoundness.lean:368–374, 475–516`):
```lean
def WV (S : Prog → Prog → Prop) : Formula → Prop
  | .plays p q a => (a = .C ∧ S p q) ∨ (Formula.plays p q a).interp
  | .impl α β => WV S α → WV S β
  | .neg φ => ¬ WV S φ
  | .box n φ => Pf n φ
  | .eq p q => p = q
  | .diag g φ => Pf g (.diag g φ) → WV S φ

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
    (h_tvote : ∀ me oppo v θ P Q, (S me oppo ∨ S' me oppo) →
      (Prog.tvote v θ P Q = me ∨ me = .bot (.tvote v θ P Q)) → False)
    (h_sys : ∀ me oppo defs i, (S me oppo ∨ S' me oppo) →
      (Prog.sys defs i = me ∨ me = .bot (.sys defs i)) → False)
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
        (k ≤ B → φ.interp) ∧ ((∀ K χ, Pf K χ → χ.interp) → WV S φ))
```
Proof structure: `Nat.strong_induction_on B`, two passes over the raw `PlaysProof.rec`/`Pf.rec` (`:517–543`); the `search_f` arm uses the floor — the refuted guard's hypothetical proof at budget `k < n+m+k+c_node ≤ B` is handled by the strong IH. Auxiliary: `eval_mono` (`:63`), `eval_mono_le` (`:130`), `eval_det` (`:139`), `VoteAllRun` (`:149–153`).

---

## (5) Finiteness / decidability facts

### Size bounds from `Pf` (`Decidability/T31EngineDecider.lean`, `T48CutRelevance.lean`)
```lean
theorem pf_size_or_atom : ∀ {k φ}, Pf k φ → φ.size ≤ k ∨ AtomProvable k φ        -- T31:176
theorem pf_impl_size {k : Nat} {A B : Formula}
    (h : Pf k (.impl A B)) : (Formula.impl A B).size ≤ k                          -- T31:216
theorem pf_pos {m : Nat} {φ : Formula} (h : Pf m φ) : 1 ≤ m                        -- T48:673
theorem box_inversion {m b : Nat} {ψ : Formula} (h : Pf m (.box b ψ)) :
    (∃ mIn, Pf mIn ψ ∧ mIn ≤ b ∧ b + (Formula.box b ψ).size ≤ m) ∨
    (∃ m₁ m₂ φ', Pf m₁ (.impl φ' (.box b ψ)) ∧ Pf m₂ φ' ∧
      m₁ + m₂ + (Formula.box b ψ).size ≤ m)                                       -- T48:683
```
So **`Pf k φ` bounds `φ.size ≤ k` EXCEPT when `φ` is a `.plays` atom** (an atom's budget bounds eval-step cost, not characters). Literal bounds (T48 §1–2; `maxLitP/maxLitF` in `T42PfB.lean:54–71` = largest `.search` budget / `.box`,`.diag` subscript):
```lean
theorem maxLitP_lt_two_pow_size : ∀ p : Prog, maxLitP p < 2 ^ p.size              -- T48:27
theorem maxLitF_lt_two_pow_size : ∀ φ : Formula, maxLitF φ < 2 ^ φ.size            -- T48 (mutual, §1)
theorem cut_lit_bound {a : Nat} {A ψ : Formula} (h : Pf a (.impl A ψ)) :
    maxLitF A < 2 ^ a ∧ maxLitF ψ < 2 ^ a                                          -- :139
theorem box_lit_bound {m a : Nat} {ψ : Formula} (h : Pf m (.box a ψ)) :
    a < 2 ^ m ∧ maxLitF ψ < 2 ^ m                                                  -- :152
theorem diag_lit_bound {m fb : Nat} {t : Formula}
    (h : Pf m (.impl (.box fb t) t)) : fb < 2 ^ m                                  -- :167
theorem local_lit_bound {m : Nat} {B : Formula} (h : Pf m B) :
    maxLitF B < 2 ^ m ∨ ∃ p q a, B = .plays p q a                                  -- :178
```

### Semidecidability — absolute (`T31` §5–8)
```lean
def decProv (O : Nat → Formula → Bool) : Nat → Nat → Formula → Bool               -- :1215
  | 0, _, _ => false
  | fuel+1, k, φ =>
      chkLeaf k φ || O k φ || chkWeaken … || chkSTS … || chkITrans … || chkAtomBox O k φ ||
      chkBoxIntroE … || chkAppE … || chkAxK … || chkBox4E k φ || chkDiagFE … || chkDiagBE … ||
      chkAxKfE k φ || chkImpS2E … || chkBoxMonoE k φ || chkAtomNeg O k φ
def decCertG (D : Nat → Formula → Bool) : Nat → Nat → Prog → Prog → Prog → Action → Bool   -- :2006 (arms: const/self/opp/bot/sim/ite/search)
def certOG (D : Nat → Formula → Bool) (fuel : Nat) : Nat → Formula → Bool             -- :2034
def decFull : Nat → Nat → Formula → Bool                                             -- :2041
  | 0 => fun _ _ => false
  | fuel+1 => decProv (certOG (decFull fuel) fuel) (fuel+1)
theorem decFull_sound : ∀ fuel k φ, decFull fuel k φ = true → Pf k φ                 -- :2117
theorem decFull_mono : ∀ f₁ f₂, f₁ ≤ f₂ → ∀ k φ, decFull f₁ k φ = true → decFull f₂ k φ = true   -- :2177
theorem decFull_complete : ∀ {m φ}, Pf m φ → ∀ K, m ≤ K → ∃ fuel, decFull fuel K φ = true   -- :2207
theorem Pf_iff_decFull (k : Nat) (φ : Formula) :
    Pf k φ ↔ ∃ fuel, decFull fuel k φ = true                                          -- :2703
```

### Computable evaluation `evalG` (`T31` §9)
```lean
def GuardSound (G : Nat → Formula → Option Bool) : Prop :=
  ∀ k φ b, G k φ = some b → proofSearch k φ = b                                       -- :2730
def guardFull (fuelD : Nat) : Nat → Formula → Option Bool                             -- :2736
theorem guardFull_sound (fuelD : Nat) : GuardSound (guardFull fuelD)                  -- :2741
def guardFast (fuelD : Nat) : Nat → Formula → Option Bool                             -- :2761  (plays-atom guards only)
def guardFastN (fuelD : Nat) : Nat → Formula → Option Bool                            -- :2811  (+ .neg plays, + size floor `k < φ.size ⇒ some false`)
theorem guardFastN_sound (fuelD : Nat) : GuardSound (guardFastN fuelD)                -- :2828

def evalG (G : Nat → Formula → Option Bool) : Nat → (me opponent body : Prog) → Option Action   -- :2889
  | 0, _, _, _ => none
  | n+1, me, opponent, body => match body with
    | .const a => some a
    | .self => evalG G n me opponent me
    | .opp => evalG G n me opponent opponent
    | .bot p => evalG G n me opponent p
    | .sim p q => let p' := p.subst me opponent; let q' := q.subst me opponent; evalG G n p' q' p'
    | .ite b a p q => match evalG G n me opponent b with
        | some r => if r == a then evalG G n me opponent p else evalG G n me opponent q
        | none => none
    | .search k φ p q => match G k (φ.subst me opponent) with
        | some true => evalG G n me opponent p
        | some false => evalG G n me opponent q
        | none => none
theorem evalG_sound (G : Nat → Formula → Option Bool) (hG : GuardSound G) :
    ∀ n me opponent body a, evalG G n me opponent body = some a →
      eval n me opponent body = some a                                                -- :2913  (SAME fuel)
def playG …  def outcomeG …                                                           -- :2957, :2961
theorem outcomeG_sound (G) (hG : GuardSound G) (fuel : Nat) (p q : Prog) (o : Outcome) :
    outcomeG G fuel p q = some o → outcome fuel p q = some o                          -- :2972
```
**Coverage caveat (verified in source):** `evalG` (`:2889–2908`), `decCertG` (`:2006–2031`), `maxLitP` (`T42:54–61`) and the whole `Decidability/` chain have **no arms for `.tvote`/`.sys`/`.selfIdx`** (`grep` returns nothing in `Decidability/`). `lakefile.toml` header: "Metatheory UNPINNED from the default build 2026-08-11: the tau constructors (`tvote`, `sys`, `selfIdx`) have no arms in the T31–T54 chain yet — that migration is debt M2"; `defaultTargets = ["PrisonersDilemma", "OutcomeCheck"]`. `TAUBOTS.md:234` lists this as debt 1 (“compounding since 08-11”). So `Pf_iff_decFull`, `evalG_sound`, the T4 decidability results are stated against the pre-tau `Prog`; against the CURRENT engine the Metatheory target is not in the default build and would not compile as-is (non-exhaustive matches).

### Is full `Pf k φ` decidable? Exactly what is proven / open
- **Proven:** `Pf` is r.e. with a verified enumerator (`Pf_iff_decFull`, no oracle). Decidability of GATED strata:
  ```lean
  -- T47Stabilization.lean:1001
  def decidePfG (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
      (hargs₀ : ∀ P ∈ playsArgsF φ₀, P ∈ AP r₁ r₂ N k₀ φ₀) :
      Decidable (PfG (modestGate N) k₀ φ₀)
  -- T53StabInst.lean:779
  def decidePfG_inst (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
      (hargs₀ : ∀ P ∈ playsArgsF φ₀, P ∈ AP r₁ r₂ N k₀ φ₀) :
      Decidable (PfG (instGate (PP r₁ r₂) N) k₀ φ₀)
  ```
  `PfG G` = gate-parametric `Pf` (`T42PfB.lean:76ff`), `modestGate N` (`T44:43`), `instGate P N` (`T50:174`); `Pf_exists_PfB : Pf k φ → ∃ N, PfB N k φ` (`T42:484`).
- **The conjecture and its status** (`T42PfB.lean:641–648`):
  ```lean
  def CutRelevance (N₀ : Nat → Formula → Nat) : Prop := ∀ k φ, Pf k φ → PfB (N₀ k φ) k φ
  theorem Pf_iff_PfB_of_cutRelevance {N₀} (hcr : CutRelevance N₀) (k φ) : Pf k φ ↔ PfB (N₀ k φ) k φ
  ```
  **FALSE at the modest gate** (`T51Regress.lean:474`):
  ```lean
  theorem cutRelevance_modestGate_false :
      (∃ m, Pf m tgtD) ∧ ∀ (N m : Nat), ¬ T42.PfG (T44.modestGate N) m tgtD
  ```
  (`tgtD` = the DupocBot self-cooperation fact; proved via bounded Löb but blocked at every modest stratum.)
- **Open frontier** (`CUT_RELEVANCE.md:3–10`, `DECIDABILITY_ROADMAP.md:72–77`): the *universal closure* `Pf k φ → PfG (instGate P N₀) k φ` for ARBITRARY minimal proofs — i.e. a computable `N₀` with `⊢_k φ ⟹ ⊢^{G}_k φ`. Only zoo-shaped derivations are certified into the instance stratum (T54). Full decidability of `Pf k φ` is therefore **not proven**; `eval` is computable relative to certificates (`evalG` + `guardFast*`), `none` remaining at the Löb boundary (`T31:3026–3030`). Roadmap: "If it fails, `Provable` is a candidate undecidable bounded-provability predicate."

---

## (6) `BoundedGL` — `Base/BoundedGL.lean:98–173` verbatim
```lean
structure BoundedGL (Sent : Type) where
  imp  : Sent → Sent → Sent
  box  : Nat → Sent → Sent
  diag : Nat → Sent → Sent
  size : Sent → Nat
  Proves : Nat → Sent → Prop
  mono : ∀ {k₁ : Nat} {φ : Sent}, Proves k₁ φ → ∀ {k₂ : Nat}, k₁ ≤ k₂ → Proves k₂ φ
  mp : ∀ {k : Nat} (m₁ m₂ : Nat) (φ α : Sent),
    Proves m₁ (imp φ α) → Proves m₂ φ → m₁ + m₂ + size α ≤ k → Proves k α
  implTrans : ∀ {k : Nat} (φ ψ χ : Sent) (a b : Nat),
    Proves a (imp φ ψ) → Proves b (imp ψ χ) → a + b + size (imp φ χ) ≤ k →
    Proves k (imp φ χ)
  impS2 : ∀ (φ ψ χ : Sent) (m₁ m₂ K : Nat),
    Proves m₁ (imp φ (imp ψ χ)) → Proves m₂ (imp φ ψ) → m₁ + m₂ + size (imp φ χ) ≤ K →
    Proves K (imp φ χ)
  boxIntro : ∀ (kIn K : Nat) (φ : Sent),
    Proves kIn φ → kIn + size (box kIn φ) ≤ K → Proves K (box kIn φ)
  axKf : ∀ (a b c K : Nat) (φ α : Sent),
    a + b + size α ≤ c →
    size (imp (box a (imp φ α)) (imp (box b φ) (box c α))) ≤ K →
    Proves K (imp (box a (imp φ α)) (imp (box b φ) (box c α)))
  box4 : ∀ (a b K : Nat) (φ : Sent),
    a + size (box a φ) ≤ b →
    size (imp (box a φ) (box b (box a φ))) ≤ K →
    Proves K (imp (box a φ) (box b (box a φ)))
  boxMono : ∀ (a b K : Nat) (φ : Sent),
    a ≤ b → size (imp (box a φ) (box b φ)) ≤ K → Proves K (imp (box a φ) (box b φ))
  diagF : ∀ (pm fb g K : Nat) (tgt : Sent),
    Proves pm (imp (box fb tgt) tgt) →
    pm + size (imp (diag g tgt) (imp (box g (diag g tgt)) tgt)) ≤ K →
    Proves K (imp (diag g tgt) (imp (box g (diag g tgt)) tgt))
  diagB : ∀ (pm fb g K : Nat) (tgt : Sent),
    Proves pm (imp (box fb tgt) tgt) →
    pm + size (imp (imp (box g (diag g tgt)) tgt) (diag g tgt)) ≤ K →
    Proves K (imp (imp (box g (diag g tgt)) tgt) (diag g tgt))

structure BoundedGL.SizeExact {Sent : Type} (B : BoundedGL Sent) : Prop where
  size_imp  : ∀ φ ψ, B.size (B.imp φ ψ) = B.size φ + B.size ψ + 1
  size_box  : ∀ k φ, B.size (B.box k φ) = numCost k + B.size φ + 1
  size_diag : ∀ g φ, B.size (B.diag g φ) = numCost g + B.size φ + 1

def pfBoundedGL : BoundedGL Formula where
  imp := .impl
  box := .box
  diag := .diag
  size := Formula.size
  Proves := Pf
  mono := Pf_mono
  mp := Pf.mp
  implTrans := Pf.implTrans
  impS2 := Pf.impS2
  boxIntro := Pf.boxIntro
  axKf := Pf.axKf
  box4 := Pf.box4
  boxMono := Pf.boxMono
  diagF := Pf.diagF
  diagB := Pf.diagB

theorem pfBoundedGL_sizeExact : pfBoundedGL.SizeExact := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
```
Excluded from the interface by design (`:38–42`): `neg`, `contrapose/negElim/implK/implS/implRefl/weakenImpl`, rule-form `axK`, and every reading rule incl. `atom`/`atomBoxImpl`. Generic theorems: `BoundedGL.mutual_loeb` (`:182`, 15 H-conditions), `BoundedGL.bloeb` (`:226`, 21 H-conditions, no size law), `BoundedGL.pblt` / `pblt_bounded` (`:290`, `:310`, need `SizeExact`; hypothesis `hsz : ∀ k, k > k₁ → 8192 * (pm k + B.size (φ k) + Nat.log2 (f k) + 8) ≤ f k`). Identity canaries `:338–341`: `@mutual_loeb = pfBoundedGL.mutual_loeb := rfl`, `@bloeb_engine = pfBoundedGL.bloeb := rfl`, `@pblt_engine = pfBoundedGL.pblt pfBoundedGL_sizeExact := rfl`, `@pblt_engine_bounded = … := rfl`. The arithmetized (PA) model is the stated, unfilled obligation (`:76–82`); no `axiom`.

### `Base/Loeb.lean` — statement heads (proof bodies omitted)
```lean
theorem mutual_loeb (A B : Formula) (kP kD fb n m c pA pB : Nat) (d₁ … d₉ K : Nat)
    (legPD : Pf pA (.impl (.box kP A) B)) (legDP : Pf pB (.impl (.box kD B) A))
    (H1 : fb ≤ kP) … (H15 : d₉ + pB + (Formula.impl (.box fb A) A).size ≤ K) :
    Pf K (.impl (.box fb A) A)                                                          -- :34–54 (H2–H14 verbatim in file; identical to BoundedGL.mutual_loeb with B.size/B.imp/B.box → Formula)
theorem bloeb_engine (φ : Formula) (pm fb g n₁ n₃ n₄ n₅ : Nat) (c₁ … c₁₄ K : Nat)
    (hLoeb : Pf pm (.impl (.box fb φ) φ)) (H1 … H21) : Pf K φ                              -- :94–122
theorem pblt_engine (φ : Nat → Formula) (f pm : Nat → Nat) (k₁ : Nat)
    (hLoeb : ∀ k, k > k₁ → Pf (pm k) (.impl (.box (f k) (φ k)) (φ k)))
    (hsz : ∀ k, k > k₁ → 8192 * (pm k + (φ k).size + Nat.log2 (f k) + 8) ≤ f k) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Pf m (φ k)                                                  -- :172
theorem pblt_engine_bounded … : ∃ k₂, ∀ k, k > k₂ → ∃ m, 2 * m ≤ f k ∧ Pf m (φ k)          -- :199
theorem pblt_engine_id (φ : Nat → Formula) (pm : Nat → Nat) (k₁ : Nat)
    (hφ : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000)
    (hpm : ∀ k, pm k ≤ 100 * Nat.log2 k + 1000)
    (hLoeb : ∀ k, k > k₁ → Pf (pm k) (.impl (.box k (φ k)) (φ k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Pf m (φ k)                                                  -- :242
theorem pblt_engine_id_bounded … : ∃ k₂, ∀ k, k > k₂ → ∃ m, 2 * m ≤ k ∧ Pf m (φ k)          -- :219
theorem mutual_pblt_engine_id (Af Bf : Nat → Formula) (p₁ p₂ : Nat → Nat) (k₁ : Nat)
    (hsA hsB : ∀ k, (·).size ≤ 100 * Nat.log2 k + 1000) (hp1 hp2 : ∀ k, pᵢ k ≤ 100 * Nat.log2 k + 1000)
    (hL1 : ∀ k, k > k₁ → Pf (p₁ k) (.impl (.box k (Af k)) (Bf k)))
    (hL2 : ∀ k, k > k₁ → Pf (p₂ k) (.impl (.box k (Bf k)) (Af k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Pf m (Af k)                                                 -- :266
theorem mutual_pblt_engine_staggered (Af Bf) (kP : Nat → Nat) (p₁ p₂) (k₁)
    (hkP : ∀ k, k ≤ kP k) (hkPlog : ∀ k, Nat.log2 (kP k) ≤ Nat.log2 k + 8) (hsA hsB hp1 hp2 as above)
    (hL1 : ∀ k, k > k₁ → Pf (p₁ k) (.impl (.box (kP k) (Af k)) (Bf k)))
    (hL2 : ∀ k, k > k₁ → Pf (p₂ k) (.impl (.box k (Bf k)) (Af k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Pf m (Af k)                                                 -- :317
theorem loeb_premise_under_box (S T : Formula) (u w fb m c p K : Nat)
    (P : Pf p (.impl (.box u S) (.impl (.box w T) T)))
    (Hm : u + (Formula.box u S).size ≤ m) (Hc : fb + m + T.size ≤ c) (Hcw : c ≤ w)
    (HK : 1024 * ((Formula.box u S).size + T.size + numCost fb + numCost m + numCost c + numCost w + p + 8) ≤ K) :
    Pf K (.impl (.box fb (.impl (.box u S) T)) (.impl (.box u S) T))                     -- :449
theorem vector2_full_pblt_engine (Af Bf) (p₁ p₂) (k₁ C D : Nat) (hsA hsB hp1 hp2 : … ≤ C * Nat.log2 k + D)
    (hL1 : ∀ k, k > k₁ → Pf (p₁ k) (.impl (.box k (Af k)) (.impl (.box k (Bf k)) (Af k))))
    (hL2 : ∀ k, k > k₁ → Pf (p₂ k) (.impl (.box k (Af k)) (.impl (.box k (Bf k)) (Bf k)))) :
    ∃ k₂, ∀ k, k > k₂ → (∃ m, Pf m (Af k)) ∧ (∃ m, Pf m (Bf k))                          -- :494
```

---

## Cross-cutting facts worth flagging
- Zero project axioms; `proofSearch := decide (Pf k φ)` is classical (`open Classical`, `ProofSystem.lean:4`) — the only source of `noncomputable` in `eval`.
- Cost model is transcript-cumulative: every leaf pays its conclusion's `Formula.size`; every combining rule pays premises + conclusion; `search_f` pays `n + m + k + c_node` (full failed budget `k` + refutation transcript `m`) — the floor forced by consistency and by budget-strong-induction soundness (`ProofSystem.lean:195–204`, `Soundness.lean:80–96`).
- `.box`'s interpretation is `Pf` itself both in `Formula.interp` and in `WV`; `.diag g φ` interprets as `Pf g (.diag g φ) → φ.interp` by definition; `diagF`/`diagB` are gated on a held Löb premise `Pf pm (.impl (.box fb tgt) tgt)` (gate kept for the exclusion censuses, `BoundedGL.lean:44–51`).
- `Metatheory` (T31–T54) is stated over the pre-2026-08-11 `Prog` (no `tvote/sys/selfIdx` arms) and is unpinned from the default build — debt M2.