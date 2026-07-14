import PrisonersDilemma.Decidability.T53StabInst
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.LlmGenerations.DIMCID

/-!
# The certified zoo.

Concrete `ProvT` trees for the zoo's oracle facts, each passing the instance
gate RAW (no excision) and kernel-sealed into `PfG (instGate …)`:

  * `dupoc_selfcoop_certified` (T50) — plays-atom Löb fixpoint;
  * `prudent_dupoc_certified` — PrudentBot (2k+64) × DupocBot k staggered mutual
    Löb (`mutualLoebT` + `bloebT` at the V-multiple budget recipe), with the
    `search_f` prudence certificate;
  * `botdupoc_prudent_certifiedA` / `justbot_guard_certified` — JustBot's chain:
    the bot-wrapped mutual pair and the guard fact JustBot's oracle consults;
  * `cimcic_coop_certified` / `dimcid_defect_certified` — the impl guards
    (`weakenImpl` over an atom; cut-free);
  * `cupodtroll_eq_certified` — the eq guard (`eqRefl`; cut-free).

Together with `decideProvableG_inst` (T53): the zoo's oracle facts live in a
decidable stratum, certificate by certificate — every guard shape, every Löb
pattern, every refutation route the zoo uses.
-/

namespace PD.T54
open PD PD.Bots PD.T31 PD.T42 PD.T43 PD.T44 PD.T49 PD.T50 PD.T52

/-- `BaseTheorems.mutual_loeb`, mirrored into the Type layer verbatim. -/
def mutualLoebT (A B : Formula) (kP kD fb n m c pA pB : Nat)
    (d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ K : Nat)
    (legPD : ProvT pA (.impl (.box kP A) B))
    (legDP : ProvT pB (.impl (.box kD B) A))
    (H1 : fb ≤ kP)
    (H2 : (Formula.impl (.box fb A) (.box kP A)).size ≤ d₁)
    (H3 : d₁ + pA + (Formula.impl (.box fb A) B).size ≤ d₂)
    (H4 : d₂ ≤ n)
    (H5 : n + (Formula.box n (.impl (.box fb A) B)).size ≤ d₃)
    (H6 : n + m + B.size ≤ c)
    (H7 : (Formula.impl (.box n (.impl (.box fb A) B))
            (.impl (.box m (.box fb A)) (.box c B))).size ≤ d₄)
    (H8 : d₄ + d₃ + (Formula.impl (.box m (.box fb A)) (.box c B)).size ≤ d₅)
    (H9 : fb + (Formula.box fb A).size ≤ m)
    (H10 : (Formula.impl (.box fb A) (.box m (.box fb A))).size ≤ d₆)
    (H11 : d₆ + d₅ + (Formula.impl (.box fb A) (.box c B)).size ≤ d₇)
    (H12 : c ≤ kD)
    (H13 : (Formula.impl (.box c B) (.box kD B)).size ≤ d₈)
    (H14 : d₇ + d₈ + (Formula.impl (.box fb A) (.box kD B)).size ≤ d₉)
    (H15 : d₉ + pB + (Formula.impl (.box fb A) A).size ≤ K) :
    ProvT K (.impl (.box fb A) A) :=
  let s1 : ProvT d₁ (.impl (.box fb A) (.box kP A)) := .boxMono fb kP d₁ A H1 H2
  let s2 : ProvT d₂ (.impl (.box fb A) B) :=
    .implTrans _ _ _ d₁ pA s1 legPD H3
  let s3 : ProvT d₃ (.box n (.impl (.box fb A) B)) :=
    .boxIntro n d₃ _ (s2.mono H4) H5
  let s4 : ProvT d₄ (.impl (.box n (.impl (.box fb A) B))
      (.impl (.box m (.box fb A)) (.box c B))) :=
    .axKf n m c d₄ (.box fb A) B H6 H7
  let s5 : ProvT d₅ (.impl (.box m (.box fb A)) (.box c B)) :=
    .app d₅ d₄ d₃ _ _ s4 s3 H8
  let s6 : ProvT d₆ (.impl (.box fb A) (.box m (.box fb A))) :=
    .box4 fb m d₆ A H9 H10
  let s7 : ProvT d₇ (.impl (.box fb A) (.box c B)) :=
    .implTrans _ _ _ d₆ d₅ s6 s5 H11
  let s8 : ProvT d₈ (.impl (.box c B) (.box kD B)) := .boxMono c kD d₈ B H12 H13
  let s9 : ProvT d₉ (.impl (.box fb A) (.box kD B)) :=
    .implTrans _ _ _ d₇ d₈ s7 s8 H14
  .implTrans _ _ _ d₉ pB s9 legDP H15

/-! ## The concrete pair. -/

def kZ : Nat := 536870912   -- 2^29
def kP : Nat := 2 * kZ + 64
def PB : Prog := Bots.PrudentBot kP
def DB : Prog := Bots.DupocBot kZ
def phiP : Formula := .plays PB DB .C     -- Prudent cooperates with Dupoc
def phiD : Formula := .plays DB PB .C     -- Dupoc cooperates with Prudent

#eval Nat.log2 kZ
#eval phiP.size
#eval phiD.size

/-- The refutation: "botDefect cooperates with Dupoc" is false — botDefect's actual
    bot∘const defection certificate. -/
def refuteT : ProvT (Nat.log2 kZ + 13) (.neg (.plays (.bot Bots.DefectBot) DB .C)) :=
  ProvT.atomNeg (.bot Bots.DefectBot) DB .D .C 2
    (AtomT.mk (PlaysT.bot PlaysT.const) (by decide))
    (by decide) (by decide)

/-- Dupoc's prudence certificate: the `search_f` floor over the refutation. -/
def prudenceT : ProvT (kZ + Nat.log2 kZ + 15) (.plays DB (.bot Bots.DefectBot) .D) :=
  ProvT.atom (AtomT.mk
    (PlaysT.search_f (k := kZ) (φ := .plays .opp .self .C) (p := .const .C)
      refuteT PlaysT.const)
    (by decide))

#eval "prudence ok"

/-- Leg 1 (staggered): PrudentBot's stacked-search read, citing the prudence
    certificate at `c_guard` cost. -/
def legPDT : ProvT 1570 (.impl (.box kP phiD) phiP) :=
  ProvT.searchThenSearch_t kP kP (kZ + Nat.log2 kZ + 15)
    (.plays .opp .self .C) (.plays .opp (.bot Bots.DefectBot) .D)
    .C .D (.const .D) PB DB rfl
    prudenceT (by decide) (by decide)

/-- Leg 2: Dupoc's `searchBranch` leaf. -/
def dLegDP : Derivation (.impl (.box kZ phiP) phiD) :=
  .searchBranch kZ (.plays .opp .self .C) .C .D DB PB rfl

#eval dLegDP.size
#eval c_guard kP

def legDPT : ProvT 254 (.impl (.box kZ phiP) phiD) :=
  .struct dLegDP (by decide)

/-- The V-multiple unit (consumer recipe): p₁+p₂+|Af|+|Bf|+log2 k+16. -/
def VZ : Nat := 1570 + 254 + 111 + 111 + 29 + 16
/-- The lowered Löb subscript: `fb + 64V = kZ`. -/
def fbZ : Nat := kZ - 64 * VZ

/-- The lowered mutual-Löb premise: `□_fb φD → φD`. -/
def premT : ProvT (160 * VZ) (.impl (.box fbZ phiD) phiD) :=
  mutualLoebT phiD phiP kP kZ fbZ (16 * VZ) (fbZ + 8 * VZ) (fbZ + 32 * VZ)
    1570 254
    (8 * VZ) (16 * VZ) (32 * VZ) (16 * VZ) (64 * VZ) (16 * VZ) (96 * VZ)
    (8 * VZ) (128 * VZ) (160 * VZ)
    legPDT legDPT
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- **THE FLAGSHIP TREE**: Dupoc cooperates with Prudent — the staggered mutual-Löb
    fact, as a concrete ProvT tree. -/
def treePD : ProvT (32768 * VZ) phiD :=
  PD.T50.bloebT phiD (160 * VZ) fbZ
    (8192 * VZ) (512 * VZ) (16384 * VZ) (16384 * VZ) (65536 * VZ)
    (256 * VZ) (256 * VZ) (1024 * VZ) (512 * VZ) (2048 * VZ) (512 * VZ) (512 * VZ)
    (3072 * VZ) (4096 * VZ) (256 * VZ) (5120 * VZ) (6144 * VZ) (7168 * VZ)
    (16384 * VZ) (32768 * VZ)
    premT
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

-- THE VERDICT: does the raw staggered cross-bot tree pass the instance gate?
#eval s!"PrudentBot×DupocBot raw tree passes instance gate: {
  treePD.gateOKb (instOKb [PB, DB] kP)}"

/-- **CERTIFIED**: the engine's marquee cross-bot result — PrudentBot (2k+64) ×
    DupocBot k staggered cooperation — lands in the instance-gated stratum. -/
theorem prudent_dupoc_certified :
    T42.PfG (instGate [PB, DB] kP) (32768 * VZ) phiD :=
  ProvT.toG treePD
    (ProvT.gateOKb_sound (fun _ hb => instOKb_iff.mp hb) treePD (by decide))

/-- And soundness closes the loop: the certified tree really is the engine fact. -/
theorem prudent_dupoc_provable : Pf (32768 * VZ) phiD :=
  ProvT.sound treePD

/-! ## The impl-guard shape: CIMCIC vs CooperateBot.

The ONE impl-shaped guard in the zoo (`impl atom atom`, CIMCIC/DIMCID) — the shape
every middle-analysis pointed at. Its guard instance is provable by `weakenImpl`
over the consequent atom, and the tree is cut-free: it certifies trivially. -/

def kC : Nat := 1000
def CB : Prog := Bots.CIMCIC kC
def guardCC : Formula :=
  .impl (.plays CB Bots.CooperateBot .C) (.plays Bots.CooperateBot CB .C)

/-- The impl-guard instance tree: `weakenImpl` over CooperateBot's const atom. -/
def treeCC : ProvT kC guardCC :=
  .weakenImpl _ _ 2
    (ProvT.atom (AtomT.mk (PlaysT.const) (by decide)))
    (by decide)

#eval s!"CIMCIC impl-guard tree passes instance gate: {
  treeCC.gateOKb (instOKb [CB] kC)}"

/-- **CERTIFIED**: the zoo's impl-guard shape lands in the instance stratum. -/
theorem cimcic_coop_certified :
    T42.PfG (instGate [CB] kC) kC guardCC :=
  ProvT.toG treeCC
    (ProvT.gateOKb_sound (fun _ hb => instOKb_iff.mp hb) treeCC (by decide))

/-! ## The eq-guard shape: CupodTrollBot recognizing CupodBot. -/

def kT : Nat := 1000
def CPB : Prog := Bots.CupodBot kT
/-- The troll's guard instance against the real CupodBot: `.eq CupodBot CupodBot`
    (the LHS is the substituted opponent probe; the RHS is the frozen literal). -/
def guardTT : Formula := .eq CPB CPB

def treeTT : ProvT 200 guardTT :=
  .struct (Derivation.eqRefl CPB) (by decide)

#eval s!"CupodTroll eq-guard tree passes instance gate: {
  treeTT.gateOKb (instOKb [CPB] kT)}"

/-- **CERTIFIED**: the eq-guard shape (source-code recognition) lands in the
    instance stratum. Coverage of the certified zoo's guard shapes is now
    complete: plays-atom Löb (T50), stacked-search + `search_f` prudence (T54),
    impl guards (T54), eq guards (here); `atomNeg` refutations exercised inside
    the prudence certificate. DIMCID is symmetric to CIMCIC. -/
theorem cupodtroll_eq_certified :
    T42.PfG (instGate [CPB] kT) 200 guardTT :=
  ProvT.toG treeTT
    (ProvT.gateOKb_sound (fun _ hb => instOKb_iff.mp hb) treeTT (by decide))

/-! ## The JustBot chain: the (botDupoc, Prudent) staggered mutual pair.

JustBot's guard asks about `.bot (DupocBot k)`; its cooperation rests on the
mutual pair Af = "botDupoc cooperates with Prudent", Bf = "Prudent cooperates
with botDupoc". Same V-recipe, `.bot`-wrapped frames throughout. -/

def BDB : Prog := .bot DB
def phiA2 : Formula := .plays BDB PB .C
def phiB2 : Formula := .plays PB BDB .C

def refute2T : ProvT (Nat.log2 kZ + 14) (.neg (.plays (.bot Bots.DefectBot) BDB .C)) :=
  ProvT.atomNeg (.bot Bots.DefectBot) BDB .D .C 2
    (AtomT.mk (PlaysT.bot PlaysT.const) (by decide))
    (by decide) (by decide)

/-- botDupoc's prudence: the `.bot`-wrapped `search_f` floor. -/
def prudence2T : ProvT (kZ + Nat.log2 kZ + 17) (.plays BDB (.bot Bots.DefectBot) .D) :=
  ProvT.atom (AtomT.mk
    (PlaysT.bot (PlaysT.search_f (k := kZ) (φ := .plays .opp .self .C)
      (p := .const .C) refute2T PlaysT.const))
    (by decide))

def legPD2T : ProvT 1570 (.impl (.box kP phiA2) phiB2) :=
  ProvT.searchThenSearch_t kP kP (kZ + Nat.log2 kZ + 17)
    (.plays .opp .self .C) (.plays .opp (.bot Bots.DefectBot) .D)
    .C .D (.const .D) PB BDB rfl
    prudence2T (by decide) (by decide)

def dLegDP2 : Derivation (.impl (.box kZ phiB2) phiA2) :=
  .botSearchStep kZ (.plays .opp .self .C) .C .D BDB PB rfl

#eval dLegDP2.size
def legDP2T : ProvT 256 (.impl (.box kZ phiB2) phiA2) :=
  .struct dLegDP2 (by decide)

def VZ2 : Nat := 1570 + 256 + 112 + 112 + 29 + 16
def fbZ2 : Nat := kZ - 64 * VZ2

def prem2T : ProvT (160 * VZ2) (.impl (.box fbZ2 phiA2) phiA2) :=
  mutualLoebT phiA2 phiB2 kP kZ fbZ2 (16 * VZ2) (fbZ2 + 8 * VZ2) (fbZ2 + 32 * VZ2)
    1570 256
    (8 * VZ2) (16 * VZ2) (32 * VZ2) (16 * VZ2) (64 * VZ2) (16 * VZ2) (96 * VZ2)
    (8 * VZ2) (128 * VZ2) (160 * VZ2)
    legPD2T legDP2T
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- botDupoc cooperates with Prudent (Af — the mutual fixpoint output). -/
def treeA2 : ProvT (32768 * VZ2) phiA2 :=
  PD.T50.bloebT phiA2 (160 * VZ2) fbZ2
    (8192 * VZ2) (512 * VZ2) (16384 * VZ2) (16384 * VZ2) (65536 * VZ2)
    (256 * VZ2) (256 * VZ2) (1024 * VZ2) (512 * VZ2) (2048 * VZ2) (512 * VZ2)
    (512 * VZ2) (3072 * VZ2) (4096 * VZ2) (256 * VZ2) (5120 * VZ2) (6144 * VZ2)
    (7168 * VZ2) (16384 * VZ2) (32768 * VZ2)
    prem2T
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- Prudent cooperates with botDupoc (Bf = JUSTBOT'S GUARD FACT): leg 1 applied to
    the boxed fixpoint output. -/
def treeB2 : ProvT (kP + 2000) phiB2 :=
  .app (kP + 2000) 1570 (kP + 200) _ _
    legPD2T
    (.boxIntro kP (kP + 200) phiA2 (treeA2.mono (by decide)) (by decide))
    (by decide)

#eval s!"JustBot chain Af raw tree passes instance gate: {
  treeA2.gateOKb (instOKb [PB, DB, BDB] kP)}"
#eval s!"JustBot guard fact Bf raw tree passes instance gate: {
  treeB2.gateOKb (instOKb [PB, DB, BDB] kP)}"

/-- **CERTIFIED**: the botDupoc mutual fixpoint (JustBot's chain, Af). -/
theorem botdupoc_prudent_certifiedA :
    T42.PfG (instGate [PB, DB, BDB] kP) (32768 * VZ2) phiA2 :=
  ProvT.toG treeA2
    (ProvT.gateOKb_sound (fun _ hb => instOKb_iff.mp hb) treeA2 (by decide))

/-- **CERTIFIED**: JustBot's guard fact (Bf) — what JustBot's oracle consults. -/
theorem justbot_guard_certified :
    T42.PfG (instGate [PB, DB, BDB] kP) (kP + 2000) phiB2 :=
  ProvT.toG treeB2
    (ProvT.gateOKb_sound (fun _ hb => instOKb_iff.mp hb) treeB2 (by decide))

/-! ## DIMCID (symmetric impl guard). -/

def DIB : Prog := Bots.DIMCID kC
def guardDD : Formula :=
  .impl (.plays DIB Bots.DefectBot .C) (.plays Bots.DefectBot DIB .D)

def treeDD : ProvT kC guardDD :=
  .weakenImpl _ _ 2
    (ProvT.atom (AtomT.mk (PlaysT.const) (by decide)))
    (by decide)

/-- **CERTIFIED**: DIMCID's impl guard vs DefectBot. -/
theorem dimcid_defect_certified :
    T42.PfG (instGate [DIB] kC) kC guardDD :=
  ProvT.toG treeDD
    (ProvT.gateOKb_sound (fun _ hb => instOKb_iff.mp hb) treeDD (by decide))

end PD.T54
