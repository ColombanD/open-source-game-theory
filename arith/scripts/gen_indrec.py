"""gen_indrec.py — generates arith/ArithS/Necessitation/IndRecRows.lean (2026-09-15):
the rows the INDUCTION-INSTANCE recognizer (`IndRec.lean`, `ProAxm.lean`'s case (ii) `AxmIndOracle`,
`DESIGN_fragments.md` §4.10 (ii)) needs beyond the `axm` table, on the `gen_proaxm.py` template.

The recognizer is NOT Foundation's `indRec` row of `Lib/Nodes.lean` (stated over the `ℒₒᵣ`-graphs, which no
walked fact matches — the ℒₒᵣ/LAct WALL of `Lib/Bridge.lean`), but a NEW sentence `indRecL` in the vocabulary the
object proof actually has: `qqAllsDef p b m` (the `qqAlls` walk), `bsF m m b` (ONE bottom-up pass that
establishes `ℒₒᵣ`-ness and the EXACT bound-variable count together — `BsF n m p := IsSemiformula ℒₒᵣ n p ∧
m = bv p`, with the `max` of `bv` computed by the two `≤`-rows `bsAndL/R` instead of a `max` fact, and the
`- 1` of `∀/∃` by the two shape rows `bsAllS/Z`), `shiftGraph LAct b b` (`certShift` on `b`'s own dossier),
`fvSeq fv 0 m` (`fv = ⟨&0, …, &(m-1)⟩`, read off the walked vector by `fvSeqNil/Cons`), `substsGraph LAct s fv b`
(`certSubst`) and `indBodyL s K` — the induction body of `K` in NEGATION-NORMAL shape facts (what the walk of
`s = subst (fvarVec m) b` exposes: `s = x ⋎ ((∃ (K ⋏ ns)) ⋎ (∀ K))`, `x = subst c0 (neg K)`,
`ns = subst c1 (neg K)`, `c0 = ⟨⌜0⌝⟩`, `c1 = ⟨⌜#0 + 1⌝⟩`), packaged through the Σ₁ predicates
`bodyShape`/`isC0`/`isC1`/`indBodyL` so that every row stays under the witness cap `9`. Its truth
(`inductionR_of_L`, the prelude) is the ONLY place the language bridge is used, and it is used SEMANTICALLY
(`subst_LAct_eq`, `neg_LAct_eq`, `shift_LAct_eq`, `bv_LAct_eq` of `Lib/Bridge.lean`): the `ℒₒᵣ`-ness of `K`
follows from that of `s = subst (fvarVec m) b` (a subformula), so no second formation pass is needed.

Rows (all NEW except `qqAllsZero`/`qqAllsSucc`, whose `Lib`/`inst_` blocks live in `Lib/Frag.lean`/`RowInstB.lean`):
the `qqAlls` walk `qqAllsZero`, `qqAllsSucc`; the `bs` pass `bsBvar`, `bsFvar`, `bsFunc`, `bsVNil`, `bsVAdjL/R`,
`bsRel`, `bsNRel`, `bsVerum`, `bsFalsum`, `bsAndL/R`, `bsOrL/R`, `bsAllS/Z`, `bsExsS/Z`; the six CLOSED `ℒₒᵣ`
symbol rows `isFuncOR_zero/one/add/mul`, `isRelOR_eq/lt` (chain-numeral arities/codes, as `Lib/Walk.lean`'s
`LAct` ones); the `≤` step `leSuccR`; `fvSeqNil`, `fvSeqCons`; `c0Intro`, `c1Intro`, `bodyIntro`, `indBodyIntroL`,
`indRecL`. Placed at `iIdx_<row> = proAxmRowCount + k` (APPEND-ONLY after the `axm` table, SYMBOLIC in
`proAxmRowCount`), the piece table `indRecPieces` extending `proAxmPieces` entrywise, per row `imk_`/`itag_`/`iok_`
against EXPLICIT table readings — `IndRecTable` lives in `IndRec.lean`.
Run from arith/: python3 scripts/gen_indrec.py
"""
import sys, re, os, types
HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, 'gen_frag.py')).read()
_src = _src[:_src.index('\ngen_frag()\ngen_rowinstb()')].replace("if len(sys.argv) > 3:", "if False:")
G = types.ModuleType('genfrag_lib')
G.__file__ = os.path.join(HERE, 'gen_frag.py')
exec(compile(_src, G.__file__, 'exec'), G.__dict__)
A, EX, S, P, C, M, by = G.A, G.EX, G.S, G.P, G.C, G.M, G.by
ALL = G.ALL

# ---- every predicate RowInstB/Frag2Rows already fully covers (no regeneration of its codes)
for k in ('alls', 'bvG', 'termBVG', 'termBVVecG', 'listMax', 'maxG', 'subG', 'fvarVec', 'nth', 'length', 'bnumG',
          'qqAddG', 'qqMulG', 'dlenDef', 'proof', 'instBG', 'gG', 'insert', 'subset', 'fsetPi', 'fsetSigma', 'ufPi',
          'setShiftG', 'setLen', 'flenG', 'tlenG', 'tlvG', 'listSum', 'tshG', 'tsG', 'tbshG', 'tbshvG', 'eq', 'mem', 'le', 'lt',
          'axL', 'verumIntro', 'andIntro', 'orIntro', 'allIntro', 'exsIntro', 'wkRule', 'shiftRule', 'cutRule', 'axm'):
    G.PREDS[k]['have'] = set(ALL)
G.PREDS['axch'] = G.graph('(↑(Theory.Δ₁ch TAct).sigma : ArithmeticSemisentence 1)', 1, 'Paxch', 'axchFact', ['p'],
                          '(Theory.Δ₁ch TAct).sigma', lambda a: f'{a[0]} ∈ TAct.Δ₁Class', have=ALL)

# ---- the NEW predicates (their Σ₁ semisentences are defined in the prelude §0 below)
G.PREDS['bsT'] = G.graph('(↑bsTDef : ArithmeticSemisentence 3)', 3, 'PbsT', 'bsTFact', ['n', 'm', 't'],
                         'bsTDef', lambda a: f'BsT {a[0]} {a[1]} {a[2]}', simps=['bsT_defined.iff'])
G.PREDS['bsV'] = G.graph('(↑bsVDef : ArithmeticSemisentence 4)', 4, 'PbsV', 'bsVFact', ['n', 'm', 'k', 'v'],
                         'bsVDef', lambda a: f'BsV {a[0]} {a[1]} {a[2]} {a[3]}', simps=['bsV_defined.iff'])
G.PREDS['bsF'] = G.graph('(↑bsFDef : ArithmeticSemisentence 3)', 3, 'PbsF', 'bsFFact', ['n', 'm', 'p'],
                         'bsFDef', lambda a: f'BsF {a[0]} {a[1]} {a[2]}', simps=['bsF_defined.iff'])
G.PREDS['fvSeq'] = G.graph('(↑fvSeqDef : ArithmeticSemisentence 3)', 3, 'PfvSeq', 'fvSeqFact', ['w', 'j', 'm'],
                           'fvSeqDef', lambda a: f'FvSeq {a[0]} {a[1]} {a[2]}', simps=['fvSeq_defined.iff'])
G.PREDS['isC0'] = G.graph('(↑isC0Def : ArithmeticSemisentence 1)', 1, 'PisC0', 'isC0Fact', ['c'],
                          'isC0Def', lambda a: f'IsC0 {a[0]}', simps=['isC0_defined.iff'])
G.PREDS['isC1'] = G.graph('(↑isC1Def : ArithmeticSemisentence 1)', 1, 'PisC1', 'isC1Fact', ['c'],
                          'isC1Def', lambda a: f'IsC1 {a[0]}', simps=['isC1_defined.iff'])
G.PREDS['bodyShape'] = G.graph('(↑bodyShapeDef : ArithmeticSemisentence 4)', 4, 'PbodyShape', 'bodyShapeFact',
                               ['s', 'x', 'ns', 'K'], 'bodyShapeDef',
                               lambda a: f'BodyShape {a[0]} {a[1]} {a[2]} {a[3]}', simps=['bodyShape_defined.iff'])
G.PREDS['indBodyL'] = G.graph('(↑indBodyLDef : ArithmeticSemisentence 2)', 2, 'PindBodyL', 'indBodyLFact', ['s', 'K'],
                              'indBodyLDef', lambda a: f'IndBodyL {a[0]} {a[1]}', simps=['indBodyL_defined.iff'])
G.PREDS['isFuncOR'] = G.graph('(↑(ℒₒᵣ).isFunc : ArithmeticSemisentence 2)', 2, 'PisFuncOR', 'isFuncORFact', ['k', 'f'],
                              '(ℒₒᵣ).isFunc', lambda a: f'(ℒₒᵣ).IsFunc {a[0]} {a[1]}')
G.PREDS['isRelOR'] = G.graph('(↑(ℒₒᵣ).isRel : ArithmeticSemisentence 2)', 2, 'PisRelOR', 'isRelORFact', ['k', 'R'],
                             '(ℒₒᵣ).isRel', lambda a: f'(ℒₒᵣ).IsRel {a[0]} {a[1]}')

# ---- the rows whose Lib/inst_ blocks already exist (table part only)
EXISTING = ['qqAllsZero', 'qqAllsSucc']
# ---- the six CLOSED ℒₒᵣ symbol rows: Lib blocks HAND-WRITTEN in the prelude (their `models_` need `norm_num`),
#      quote_row_/inst_ blocks and table parts generated
CLOSED = [
 ('isFuncOR_zero', [], [], A('isFuncOR', 'Z', 'Z')),
 ('isFuncOR_one', [], [], A('isFuncOR', 'Z', C(1))),
 ('isFuncOR_add', [], [], A('isFuncOR', C(2), 'Z')),
 ('isFuncOR_mul', [], [], A('isFuncOR', C(2), C(1))),
 ('isRelOR_eq', [], [], A('isRelOR', C(2), 'Z')),
 ('isRelOR_lt', [], [], A('isRelOR', C(2), C(1))),
]
# ---- the NEW rows: (name, binders, ants, conc, proof, doc)
NEW_ROWS = [
 # the `bs` pass — terms
 ('bsBvar', ['t', 'z', 'n'], [A('lt', 'z', 'n'), A('qqBvar', 't', 'z')], A('bsT', 'n', S('z'), 't'),
  by('subst h₂; exact ⟨IsSemiterm.bvar.mpr h₁, (termBV_bvar _).symm⟩'),
  "`z < n → t = #z → BsT n (z + 1) t`."),
 ('bsFvar', ['t', 'x', 'n'], [A('qqFvar', 't', 'x')], A('bsT', 'n', 'Z', 't'),
  by('subst h₁; exact ⟨IsSemiterm.fvar _ _, (termBV_fvar _).symm⟩'),
  "`t = &x → BsT n 0 t`."),
 ('bsFunc', ['t', 'v', 'f', 'k', 'm', 'n'], [A('isFuncOR', 'k', 'f'), A('bsV', 'n', 'm', 'k', 'v'), A('qqFunc', 't', 'k', 'f', 'v')],
  A('bsT', 'n', 'm', 't'),
  by('obtain ⟨hv, hm⟩ := h₂; subst h₃ hm; exact ⟨IsSemiterm.func.mpr ⟨h₁, hv⟩, (termBV_func h₁ hv.isUTermVec).symm⟩'),
  "`(ℒₒᵣ).IsFunc k f → BsV n m k v → t = func k f v → BsT n m t`."),
 ('bsVNil', ['n'], [], A('bsV', 'n', 'Z', 'Z', 'Z'),
  'fun _ ↦ ⟨IsSemitermVec.nil _, by unfold termBVVec; rw [IsUTerm.BV.construction.resultVec_nil ℒₒᵣ ![]]; simp⟩',
  "`BsV n 0 0 0`: the empty vector."),
 ('bsVAdjL', ["v'", 'v', 't', 'mv', 'mt', 'k', 'n'],
  [A('bsT', 'n', 'mt', 't'), A('bsV', 'n', 'mv', 'k', 'v'), A('adjoin', "v'", 't', 'v'), A('le', 'mt', 'mv')],
  A('bsV', 'n', 'mv', S('k'), "v'"),
  by('obtain ⟨ht, hmt⟩ := h₁; obtain ⟨hv, hmv⟩ := h₂; subst h₃ hmt hmv; exact ⟨IsSemitermVec.cons_iff.mpr ⟨ht, hv⟩, by rw [termBVVec_cons ht.isUTerm hv.isUTermVec, listMax_adjoin, max_eq_right h₄]⟩'),
  "`BsT n mt t → BsV n mv k v → v' = t ∷ v → mt ≤ mv → BsV n mv (k + 1) v'` (the head does not raise the max)."),
 ('bsVAdjR', ["v'", 'v', 't', 'mv', 'mt', 'k', 'n'],
  [A('bsT', 'n', 'mt', 't'), A('bsV', 'n', 'mv', 'k', 'v'), A('adjoin', "v'", 't', 'v'), A('le', 'mv', 'mt')],
  A('bsV', 'n', 'mt', S('k'), "v'"),
  by('obtain ⟨ht, hmt⟩ := h₁; obtain ⟨hv, hmv⟩ := h₂; subst h₃ hmt hmv; exact ⟨IsSemitermVec.cons_iff.mpr ⟨ht, hv⟩, by rw [termBVVec_cons ht.isUTerm hv.isUTermVec, listMax_adjoin, max_eq_left h₄]⟩'),
  "`… → mv ≤ mt → BsV n mt (k + 1) v'` (the head raises the max)."),
 # the `bs` pass — formulas
 ('bsRel', ['p', 'v', 'R', 'k', 'm', 'n'], [A('isRelOR', 'k', 'R'), A('bsV', 'n', 'm', 'k', 'v'), A('qqRel', 'p', 'k', 'R', 'v')],
  A('bsF', 'n', 'm', 'p'),
  by('obtain ⟨hv, hm⟩ := h₂; subst h₃ hm; exact ⟨IsSemiformula.rel.mpr ⟨h₁, hv⟩, (bv_rel h₁ hv.isUTermVec).symm⟩'),
  "`(ℒₒᵣ).IsRel k R → BsV n m k v → p = rel k R v → BsF n m p`."),
 ('bsNRel', ['p', 'v', 'R', 'k', 'm', 'n'], [A('isRelOR', 'k', 'R'), A('bsV', 'n', 'm', 'k', 'v'), A('qqNRel', 'p', 'k', 'R', 'v')],
  A('bsF', 'n', 'm', 'p'),
  by('obtain ⟨hv, hm⟩ := h₂; subst h₃ hm; exact ⟨IsSemiformula.nrel.mpr ⟨h₁, hv⟩, (bv_nrel h₁ hv.isUTermVec).symm⟩'),
  "the `nrel` twin of `bsRel`."),
 ('bsVerum', ['p', 'n'], [A('qqVerum', 'p')], A('bsF', 'n', 'Z', 'p'),
  by('subst h₁; exact ⟨IsSemiformula.verum, bv_verum.symm⟩'), "`p = ⊤ → BsF n 0 p`."),
 ('bsFalsum', ['p', 'n'], [A('qqFalsum', 'p')], A('bsF', 'n', 'Z', 'p'),
  by('subst h₁; exact ⟨IsSemiformula.falsum, bv_falsum.symm⟩'), "`p = ⊥ → BsF n 0 p`."),
 ('bsAndL', ['r', 'q', 'p', 'mq', 'mp', 'n'],
  [A('bsF', 'n', 'mp', 'p'), A('bsF', 'n', 'mq', 'q'), A('qqAnd', 'r', 'p', 'q'), A('le', 'mp', 'mq')], A('bsF', 'n', 'mq', 'r'),
  by('obtain ⟨hp, hmp⟩ := h₁; obtain ⟨hq, hmq⟩ := h₂; subst h₃ hmp hmq; exact ⟨IsSemiformula.and.mpr ⟨hp, hq⟩, by rw [bv_and hp.isUFormula hq.isUFormula, max_eq_right h₄]⟩'),
  "`BsF n mp p → BsF n mq q → r = p ⋏ q → mp ≤ mq → BsF n mq r`."),
 ('bsAndR', ['r', 'q', 'p', 'mq', 'mp', 'n'],
  [A('bsF', 'n', 'mp', 'p'), A('bsF', 'n', 'mq', 'q'), A('qqAnd', 'r', 'p', 'q'), A('le', 'mq', 'mp')], A('bsF', 'n', 'mp', 'r'),
  by('obtain ⟨hp, hmp⟩ := h₁; obtain ⟨hq, hmq⟩ := h₂; subst h₃ hmp hmq; exact ⟨IsSemiformula.and.mpr ⟨hp, hq⟩, by rw [bv_and hp.isUFormula hq.isUFormula, max_eq_left h₄]⟩'),
  "`… → mq ≤ mp → BsF n mp r`."),
 ('bsOrL', ['r', 'q', 'p', 'mq', 'mp', 'n'],
  [A('bsF', 'n', 'mp', 'p'), A('bsF', 'n', 'mq', 'q'), A('qqOr', 'r', 'p', 'q'), A('le', 'mp', 'mq')], A('bsF', 'n', 'mq', 'r'),
  by('obtain ⟨hp, hmp⟩ := h₁; obtain ⟨hq, hmq⟩ := h₂; subst h₃ hmp hmq; exact ⟨IsSemiformula.or.mpr ⟨hp, hq⟩, by rw [bv_or hp.isUFormula hq.isUFormula, max_eq_right h₄]⟩'),
  "the `⋎` twin of `bsAndL`."),
 ('bsOrR', ['r', 'q', 'p', 'mq', 'mp', 'n'],
  [A('bsF', 'n', 'mp', 'p'), A('bsF', 'n', 'mq', 'q'), A('qqOr', 'r', 'p', 'q'), A('le', 'mq', 'mp')], A('bsF', 'n', 'mp', 'r'),
  by('obtain ⟨hp, hmp⟩ := h₁; obtain ⟨hq, hmq⟩ := h₂; subst h₃ hmp hmq; exact ⟨IsSemiformula.or.mpr ⟨hp, hq⟩, by rw [bv_or hp.isUFormula hq.isUFormula, max_eq_left h₄]⟩'),
  "the `⋎` twin of `bsAndR`."),
 ('bsAllS', ['r', 'p', 'mp', 'n'], [A('bsF', S('n'), S('mp'), 'p'), A('qqAll', 'r', 'p')], A('bsF', 'n', 'mp', 'r'),
  by('obtain ⟨hp, hm⟩ := h₁; subst h₂; exact ⟨IsSemiformula.all.mpr hp, by rw [bv_all hp.isUFormula, ← hm]; simp⟩'),
  "`BsF (n + 1) (mp + 1) p → r = ∀ p → BsF n mp r` (`bv (∀ p) = bv p - 1`, the positive case)."),
 ('bsAllZ', ['r', 'p', 'n'], [A('bsF', S('n'), 'Z', 'p'), A('qqAll', 'r', 'p')], A('bsF', 'n', 'Z', 'r'),
  by('obtain ⟨hp, hm⟩ := h₁; subst h₂; exact ⟨IsSemiformula.all.mpr hp, by rw [bv_all hp.isUFormula, ← hm]; simp⟩'),
  "`BsF (n + 1) 0 p → r = ∀ p → BsF n 0 r` (`0 - 1 = 0`)."),
 ('bsExsS', ['r', 'p', 'mp', 'n'], [A('bsF', S('n'), S('mp'), 'p'), A('qqExs', 'r', 'p')], A('bsF', 'n', 'mp', 'r'),
  by('obtain ⟨hp, hm⟩ := h₁; subst h₂; exact ⟨IsSemiformula.exs.mpr hp, by rw [bv_ex hp.isUFormula, ← hm]; simp⟩'),
  "the `∃` twin of `bsAllS`."),
 ('bsExsZ', ['r', 'p', 'n'], [A('bsF', S('n'), 'Z', 'p'), A('qqExs', 'r', 'p')], A('bsF', 'n', 'Z', 'r'),
  by('obtain ⟨hp, hm⟩ := h₁; subst h₂; exact ⟨IsSemiformula.exs.mpr hp, by rw [bv_ex hp.isUFormula, ← hm]; simp⟩'),
  "the `∃` twin of `bsAllZ`."),
 # the `≤` step on chain numerals
 ('leSuccR', ['b', 'a'], [A('le', 'a', 'b')], A('le', 'a', S('b')),
  'fun _ _ h₁ ↦ le_trans h₁ le_self_add', "`a ≤ b → a ≤ b + 1` (the `≤` chain between chain numerals)."),
 # `fvSeq`
 ('fvSeqNil', ['j'], [], A('fvSeq', 'Z', 'j', 'j'),
  'fun _ ↦ ⟨le_refl _, by simp, fun i hi ↦ by simp at hi⟩', "`FvSeq 0 j j`: the empty tail."),
 ('fvSeqCons', ["w'", 't', 'w', 'm', 'j'], [A('fvSeq', 'w', S('j'), 'm'), A('qqFvar', 't', 'j'), A('adjoin', "w'", 't', 'w')],
  A('fvSeq', "w'", 'j', 'm'),
  by('exact fvSeq_cons h₁ h₂ h₃'),
  "`FvSeq w (j + 1) m → t = &j → w' = t ∷ w → FvSeq w' j m`."),
 # the body
 ('c0Intro', ['c', 't'], [A('qqFunc', 't', 'Z', 'Z', 'Z'), A('adjoin', 'c', 't', 'Z')], A('isC0', 'c'),
  'fun _ _ h₁ h₂ ↦ ⟨_, h₁, h₂⟩', "`t = func 0 0 0 → c = t ∷ 0 → IsC0 c`."),
 ('c1Intro', ['c', 't', 'v2', 'x', 'v1', 'o'],
  [A('qqFunc', 'o', 'Z', C(1), 'Z'), A('adjoin', 'v1', 'o', 'Z'), A('qqBvar', 'x', 'Z'), A('adjoin', 'v2', 'x', 'v1'),
   A('qqFunc', 't', C(2), 'Z', 'v2'), A('adjoin', 'c', 't', 'Z')], A('isC1', 'c'),
  'fun _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ ⟨_, _, _, _, _, h₁, h₂, h₃, h₄, h₅, h₆⟩',
  "the six shape facts of `⟨⌜#0 + 1⌝⟩` give `IsC1 c`."),
 ('bodyIntro', ['s', 'x', 'y', 'u', 'z', 'n1', 'K', 'ns', 'K2'],
  [A('qqOr', 's', 'x', 'y'), A('qqOr', 'y', 'u', 'z'), A('qqExs', 'u', 'n1'), A('qqAnd', 'n1', 'K', 'ns'), A('qqAll', 'z', 'K2'),
   A('eq', 'K2', 'K')], A('bodyShape', 's', 'x', 'ns', 'K'),
  'fun _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ ⟨_, _, _, _, h₁, h₂, h₃, h₄, h₆ ▸ h₅⟩',
  "the five shape facts of `s = x ⋎ ((∃ (K ⋏ ns)) ⋎ (∀ K2))` and `K2 = K` give `BodyShape s x ns K`."),
 ('indBodyIntroL', ['s', 'K', 'x', 'ns', 'nk', 'c0', 'c1'],
  [A('bodyShape', 's', 'x', 'ns', 'K'), A('negG', 'nk', 'K'), A('isC0', 'c0'), A('substsG', 'x', 'c0', 'nk'), A('isC1', 'c1'),
   A('substsG', 'ns', 'c1', 'nk')], A('indBodyL', 's', 'K'),
  'fun _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ ⟨_, _, _, _, _, h₁, h₂, h₃, h₄, h₅, h₆⟩',
  "`BodyShape s x ns K → nk = neg K → IsC0 c0 → x = subst c0 nk → IsC1 c1 → ns = subst c1 nk → IndBodyL s K`."),
 ('indRecL', ['K', 's', 'fv', 'b', 'm', 'p'],
  [A('alls', 'p', 'b', 'm'), A('bsF', 'm', 'm', 'b'), A('shiftG', 'b', 'b'), A('fvSeq', 'fv', 'Z', 'm'),
   A('substsG', 's', 'fv', 'b'), A('indBodyL', 's', 'K')], A('axch', 'p'),
  'fun _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ inductionR_of_L h₁ h₂ h₃ h₄ h₅ h₆',
  "**THE RECOGNIZER**: `p = qqAlls b m → BsF m m b → b = shift b → FvSeq fv 0 m → s = subst fv b → IndBodyL s K → p ∈ TAct.Δ₁Class` — every hypothesis in the `LAct` vocabulary of the walked facts (`inductionR_of_L`)."),
]
TABLE = EXISTING + [n for (n, *_r) in CLOSED] + [n for (n, *_r) in NEW_ROWS]

# register the rows so that `used_preds` sees them
G.ROWS = [('indrec', n, b, a, c, p, d) for (n, b, a, c, p, d) in NEW_ROWS] + [('indrec', n, b, a, c, None, '') for (n, b, a, c) in CLOSED]
G.GROUPS = None

# --- generated text: Lib blocks (new rows), predicate codes, quote_row_/inst_ blocks (closed + new)
G.frag = []; G.out = []
for (name, binders, ants, conc, proof, doc) in NEW_ROWS:
    G.gen_frag_row('indrec', name, binders, ants, conc, proof, doc)
lib_blocks = '\n'.join(G.frag)
G.out = []
G.gen_preds()
pred_blocks = '\n'.join(G.out)
G.out = []
for (name, binders, ants, conc) in CLOSED:
    G.gen_row(name, binders, ants, conc)
for (name, binders, ants, conc, proof, doc) in NEW_ROWS:
    G.gen_row(name, binders, ants, conc)
new_blocks = '\n'.join(G.out)

rowinstb = open(os.path.join(HERE, '..', 'ArithS', 'Necessitation', 'RowInstB.lean')).read()
alltext = rowinstb + '\n' + new_blocks

def split_top(s):
    out=[]; d=0; cur=''
    for ch in s:
        if ch in '([': d+=1
        if ch in ')]': d-=1
        if ch==',' and d==0:
            out.append(cur.strip()); cur=''
        else: cur+=ch
    if cur.strip(): out.append(cur.strip())
    return out

info = {}
for name in TABLE:
    m = re.search(r'lemma isSemiformula_%s_c : IsSemiformula LAct \(\((\d+) : ℕ\) : V\)' % name, alltext)
    ar = int(m.group(1))
    tag2 = ('noncomputable def row_%s_R' % name) in alltext
    mi = alltext.index('lemma inst_%s ' % name)
    stmt = alltext[mi: alltext.index(':= by', mi)]
    wm = re.search(r'lemma inst_%s\s*(\{([^}]*) : V\})?' % name, stmt)
    wits = wm.group(2).split() if wm.group(2) else []
    fm = re.search(r'\.map \(instOuter LAct (?:\[[^\]]*\]|\(\[\] : List V\))\) = \[(.*?)\] ∧', stmt, re.S)
    facts = split_top(fm.group(1)) if fm.group(1).strip() else []
    cm = re.search(r'instOuter LAct (?:\[[^\]]*\]|\(\[\] : List V\)) row_%s_c = (.*)$' % name, stmt, re.S)
    conc = ' '.join(cm.group(1).split())
    assert len(wits) == ar, (name, wits, ar)
    assert not tag2
    info[name] = dict(m=ar, wits=wits, facts=facts, conc=conc)

PIECES_PREFIX = ('walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList ++ topExtraPieceList ++ '
                 'proExtraPieceList ++ numIdPadPieceList ++ numIdExtraPieceList ++ proAxmExtraPieceList')

o = []
E = o.append
E('/-! ## 4. The extra rows at `proAxmRowCount + k`, the piece table, the applicability lemmas -/')
E('')
E('section indRecRowsTable')
E('')
for k, name in enumerate(TABLE):
    E(f'def iIdx_{name} : ℕ := proAxmRowCount + {k}')
E(f'def indRecExtraRowCount : ℕ := {len(TABLE)}')
E('')
E('/-- The extra rows at `proAxmRowCount + k`, in index order (append-only). -/')
E('noncomputable def indRecExtraRows : List WRow := [')
E(',\n'.join(f'  ⟨{info[n]["m"]}, {n}B, lib_{n}⟩' for n in TABLE))
E(']')
E('')
E('lemma indRecExtraRows_length : indRecExtraRows.length = indRecExtraRowCount := rfl')
E('')
E("/-- **The recognizer table's rows**: the `axm` table's rows, then the recognizer rows. -/")
E('noncomputable def indRecRows : List WRow := proAxmRows ++ indRecExtraRows')
E('def indRecRowCount : ℕ := proAxmRowCount + indRecExtraRowCount')
E('lemma indRecRows_length : indRecRows.length = indRecRowCount := by')
E('  simp only [indRecRows, List.length_append, proAxmRows_length, indRecExtraRows_length, indRecRowCount]')
E('')
E('/-! ### The piece table -/')
E('')
for name in TABLE:
    E(f'noncomputable def ipiece_{name} : V := ⟪(0 : V), vecOf row_{name}_as, row_{name}_c⟫')
E('')
E('noncomputable def indRecExtraPieceList : List V := [')
E(',\n'.join(f'  ipiece_{n}' for n in TABLE))
E(']')
E('')
E("/-- **The piece table of the recognizer**: the `axm` table's pieces, then the extra rows' pieces. -/")
E(f'noncomputable def indRecPieces : V := vecOf ({PIECES_PREFIX} ++ indRecExtraPieceList)')
E('')
E('set_option maxHeartbeats 2000000 in')
E('lemma indRecPieces_nth_lt (i : ℕ) (hi : i < proAxmRowCount) : (indRecPieces : V).[(i : V)] = (proAxmPieces : V).[(i : V)] := by')
E('  unfold indRecPieces proAxmPieces')
E(f'  have h1 : i < ({PIECES_PREFIX} ++ indRecExtraPieceList : List V).length := by')
E(f'    rw [show ({PIECES_PREFIX} ++ indRecExtraPieceList : List V).length = indRecRowCount from rfl]')
E('    exact lt_of_lt_of_le hi (by simp only [indRecRowCount]; omega)')
E(f'  have h2 : i < ({PIECES_PREFIX} : List V).length := by')
E(f'    rw [show ({PIECES_PREFIX} : List V).length = proAxmRowCount from rfl]; exact hi')
E('  rw [nth_vecOf _ i h1, nth_vecOf _ i h2]')
E('  exact List.getElem_append_left h2')
E('')
E("/-- An `axm`-table step read from the recognizer pieces is the `axm` table's step. -/")
E('lemma mkStep_indRecPieces_lt (i : ℕ) (hi : i < proAxmRowCount) (ev : V) :')
E('    mkStep indRecPieces (i : V) ev = mkStep proAxmPieces (i : V) ev := by')
E('  rw [mkStep, mkStep, indRecPieces_nth_lt i hi]')
E('')
for name in TABLE:
    E('set_option maxHeartbeats 2000000 in')
    E(f'lemma indRecPieces_{name} : (indRecPieces : V).[((iIdx_{name} : ℕ) : V)] = ipiece_{name} := by')
    E(f'  unfold indRecPieces')
    E(f'  rw [nth_vecOf _ iIdx_{name} (Nat.lt_of_sub_eq_succ rfl)]')
    E(f'  rfl')
    E('')
    E(f'lemma imk_{name} (ev : V) :')
    E(f'    mkStep indRecPieces ((iIdx_{name} : ℕ) : V) ev = sUseHorn ((iIdx_{name} : ℕ) : V) ev (vecOf row_{name}_as) row_{name}_c := by')
    E(f'  rw [mkStep, indRecPieces_{name}]')
    E(f'  simp [ipiece_{name}, sUseHorn]')
    E('')
    E(f'lemma itag_{name} {{W : V}} (hWp : W = indRecPieces) (ev : V) : sTag (mkStep W ((iIdx_{name} : ℕ) : V) ev) = 0 := by')
    E(f'  subst hWp')
    E(f'  rw [imk_{name}]; simp')
    E('')
E('/-! ### The per-row applicability lemmas `iok_<row>` (against explicit table readings) -/')
E('')
for name in TABLE:
    d = info[name]
    ws = d['wits']; facts = d['facts']; conc = d['conc']
    Mcap = 9 if (len(ws) > 8 or len(facts) > 8) else 8
    vec = '?[' + ', '.join(ws) + ']' if ws else '0'
    lst = '[' + ', '.join(ws) + ']'
    binders = ('{' + ' '.join(ws) + ' : V} ') if ws else ''
    hyps = ' '.join(f'(h{w} : IsSemiterm LAct 0 {w}) (hE{w} : termLen LAct {w} ≤ E)' for w in ws)
    mems = ' '.join(f'(hmem{i} : neg LAct ({f}) ∈ Γ)' for i, f in enumerate(facts))
    hes_term = 'List.forall_mem_nil _'
    for w in reversed(ws):
        hes_term = f'List.forall_mem_cons.mpr ⟨⟨h{w}, hE{w}⟩, {hes_term}⟩'
    mem_term = 'List.forall_mem_nil _'
    for i in reversed(range(len(facts))):
        mem_term = f'List.forall_mem_cons.mpr ⟨hmem{i}, {mem_term}⟩'
    inst_args = ' '.join(f'h{w}' for w in ws) if ws else '(V := V)'
    idx = f'((iIdx_{name} : ℕ) : V)'
    E(f'/-- Row `{name}` as a step, against the table readings `hlen`/`hrow` at its index. -/')
    E(f'lemma iok_{name} {{tbl N E Γ W : V}} {binders}(htbl : TableOK tbl N) (hWp : W = indRecPieces)')
    E(f'    (hlen : {idx} < len tbl)')
    E(f'    (hrow : rowM tbl.[{idx}] = (({d["m"]} : ℕ) : V) ∧')
    E(f'      rowB tbl.[{idx}] = impChainV LAct (vecOf row_{name}_as) row_{name}_c)')
    E(f'    (hΓ : IsFormulaSet LAct Γ) {hyps} {mems} :')
    E(f'    StepOK tbl E (({Mcap} : ℕ) : V) Γ (mkStep W {idx} {vec}) ∧ sTag (mkStep W {idx} {vec}) = 0 ∧')
    E(f'    ctxAfter Γ (mkStep W {idx} {vec}) = insert (neg LAct ({conc})) Γ := by')
    E(f'  subst hWp')
    E(f'  have hstep := imk_{name} (V := V) {vec}')
    E(f'  have hes : ∀ e ∈ ({lst} : List V), IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := {hes_term}')
    E(f'  have hinst := inst_{name} {inst_args}')
    E(f'  rw [hstep, show ({vec} : V) = vecOf {lst} from rfl]')
    E(f'  refine ⟨stepOK_useHorn htbl {lst} row_{name}_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : {len(ws)} ≤ {Mcap}))')
    E(f'    (by rw [show row_{name}_as.length = {len(facts)} from rfl] <;> exact_mod_cast (by decide : {len(facts)} ≤ {Mcap})) hes ?_, by simp, ?_⟩')
    E(f'  · exact neg_mem_of_map hinst.1 ({mem_term})')
    E(f'  · rw [ctxAfter_useHorn {lst} row_{name}_as isSemiformula_{name}_c (fun e he ↦ (hes e he).1), hinst.2]')
    E('')
E('end indRecRowsTable')
table_part = '\n'.join(o)

header = open(os.path.join(HERE, 'IndRecRows.lean.head')).read()

mid1 = '''
/-! ## 1. The new library rows (`Lib`) -/

section indRecLib

'''
mid2 = '''
end indRecLib

'''
mid3 = '''
/-! ## 3. The `quote_row_`/`inst_` blocks (the `RowInstB` template) -/

section indRecRowInst

'''
mid4 = '''
end indRecRowInst

'''
footer = '''

end ArithS
'''
out_path = os.path.join(HERE, '..', 'ArithS', 'Necessitation', 'IndRecRows.lean')
open(out_path, 'w').write(header + mid1 + lib_blocks + mid2 + pred_blocks + mid3 + new_blocks + mid4 + table_part + footer)
print('wrote', out_path, 'rows:', TABLE)
