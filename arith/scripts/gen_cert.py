"""gen_cert.py — generates arith/ArithS/Necessitation/CertRows.lean (2026-09-13):
the ten Lib/Lengths.lean rows re-issued with quote_row_/inst_ lemmas (via gen_frag.py's gen_row), and the
certification table (cIdx_<row> = 100 + k, CertTable, exists_certTable, certPieces, per-row readings and
cok_<row> applicability lemmas). Run from arith/: python3 scripts/gen_cert.py
"""
import sys, re, os, types
HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, 'gen_frag.py')).read()
_src = _src[:_src.index('\ngen_frag()\ngen_rowinstb()')].replace("if len(sys.argv) > 3:", "if False:")
G = types.ModuleType('genfrag_lib')
G.__file__ = os.path.join(HERE, 'gen_frag.py')
exec(compile(_src, G.__file__, 'exec'), G.__dict__)
A, EX, S, P = G.A, G.EX, G.S, G.P

# ---- the ten length rows of Lib/Lengths.lean, re-issued with quote_row_/inst_ lemmas (same names, same DSL)
LEN_ROWS = [
 ('formulaLenVerum', ['l','p'], [A('qqVerum','p'), A('flenG','l','p')], A('eq','l','One')),
 ('formulaLenFalsum', ['l','p'], [A('qqFalsum','p'), A('flenG','l','p')], A('eq','l','One')),
 ('formulaLenAnd', ['lr','lq','lp','r','q','p','n'], [A('pi','n','p'), A('pi','n','q'), A('qqAnd','r','p','q'), A('flenG','lp','p'), A('flenG','lq','q'), A('flenG','lr','r')], A('eq','lr',S(P('lp','lq')))),
 ('formulaLenOr', ['lr','lq','lp','r','q','p','n'], [A('pi','n','p'), A('pi','n','q'), A('qqOr','r','p','q'), A('flenG','lp','p'), A('flenG','lq','q'), A('flenG','lr','r')], A('eq','lr',S(P('lp','lq')))),
 ('formulaLenAll', ['lq','lp','q','p','n'], [A('pi',S('n'),'p'), A('qqAll','q','p'), A('flenG','lp','p'), A('flenG','lq','q')], A('eq','lq',S('lp'))),
 ('formulaLenExs', ['lq','lp','q','p','n'], [A('pi',S('n'),'p'), A('qqExs','q','p'), A('flenG','lp','p'), A('flenG','lq','q')], A('eq','lq',S('lp'))),
 ('termLenBvar', ['l','t','z'], [A('qqBvar','t','z'), A('tlenG','l','t')], A('eq','l',S('z'))),
 ('termLenFvar', ['l','t','x'], [A('qqFvar','t','x'), A('tlenG','l','t')], A('eq','l',S('x'))),
 ('formulaLenTotal', ['p'], [], EX(['l'], [A('flenG','l','p')])),
 ('termLenTotal', ['t'], [], EX(['l'], [A('tlenG','l','t')])),
 # ---- the three rows APPENDED 2026-09-14 for `lenSteps` (sentences + `lib_` proofs hand-written in `head` §0):
 ('congAdd', ["y'", 'y', "x'", 'x'], [A('eq','x',"x'"), A('eq','y',"y'")], A('eq', P('x','y'), P("x'","y'"))),
 ('congSucc', ["x'", 'x'], [A('eq','x',"x'")], A('eq', S('x'), S("x'"))),
 ('listSumAdjI', ["s'", 's', 'l', 'M', "M'"], [A('listSum','s','M'), A('adjoin',"M'",'l','M'), A('eq', P('l','s'), "s'")], A('listSum', "s'", "M'")),
 # ---- APPENDED 2026-09-14 (later) for `certSubst`: the term-substitution left congruence (sentence + `lib_` in `head` §0):
 ('congTSubstL', ['t', 'w', "e'", 'e'], [A('eq', "e'", 'e'), A('tsG', 'e', 'w', 't')], A('tsG', "e'", 'w', 't')),
]
G.out = []
for (name, binders, ants, conc) in LEN_ROWS:
    G.gen_row(name, binders, ants, conc)
len_blocks = '\n'.join(G.out)

# ---- the table rows: (name, source) — source 'B' = RowInstB.lean, 'L' = the blocks above
TABLE = [
 'negRelCert','negNRelCert','negVerumCert','negFalsumCert','negAndCert','negOrCert','negAllCert','negExsCert',
 'shiftRelCert','shiftNRelCert','shiftVerumCert','shiftFalsumCert','shiftAndCert','shiftOrCert','shiftAllCert','shiftExsCert',
 'tshvNilCert','tshvAdjCert','termShiftBvarCert','termShiftFvarCert','termShiftFuncCert',
 'eqRefl','eqSymm','eqTrans','eqOfBvar','eqOfFvar','eqOfFunc','eqOfAdj','eqOfRel','eqOfNRel','eqOfAnd','eqOfOr','eqOfAll','eqOfExs','eqOfVerum','eqOfFalsum',
 'congRel','congNRel',
 'termLenVecNil','termLenVecAdj','listSumNil','listSumAdj','formulaLenRelCert','formulaLenNRelCert','termLenFuncCert','congLenNum','congTLenNum',
 'formulaLenVerum','formulaLenFalsum','formulaLenAnd','formulaLenOr','formulaLenAll','formulaLenExs','termLenBvar','termLenFvar','formulaLenTotal','termLenTotal',
 'substsRelCert','substsNRelCert','substsVerumCert','substsFalsumCert','substsAndCert','substsOrCert','substsAllCert','substsExsCert',
 'freeCert','substsSubsts1','tsvNilCert','termSubstBvarCert','termSubstFvarCert','termSubstFuncCert',
 'tbshvNilCert','tbshvAdjCert','termBShiftBvarCert','termBShiftFvarCert','termBShiftFuncCert',
 'qVecCert','qVecNth0','qVecNthSucc','nthAdjoinZero','nthAdjoinSucc',
 'tsvAdjCert',
 'congAdj',
 'congAdd', 'congSucc', 'listSumAdjI',
 'congTSubstL',
]
BASE = 100
rowinstb = open('ArithS/Necessitation/RowInstB.lean').read()
alltext = rowinstb + '\n' + len_blocks

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
    fm = re.search(r'\.map \(instOuter LAct [^)]*\) = \[(.*?)\] ∧', stmt, re.S)
    facts = split_top(fm.group(1)) if fm.group(1).strip() else []
    if tag2:
        cm = re.search(r'freeIter LAct 1 \(instOuterAt LAct 1 \[[^\]]*\] row_%s_body\) = (.*)$' % name, stmt, re.S)
    else:
        cm = re.search(r'instOuter LAct \[[^\]]*\] row_%s_c = (.*)$' % name, stmt, re.S)
    conc = ' '.join(cm.group(1).split())
    assert len(wits) == ar, (name, wits, ar)
    info[name] = dict(m=ar, tag2=tag2, wits=wits, facts=facts, conc=conc)

o = []
E = o.append
E('/-! ## 2. The certification table: the walk rows, a pad, then the cert/identification/length rows at `100 + k` -/')
E('')
E('section certTable')
E('')
for k, name in enumerate(TABLE):
    E(f'def cIdx_{name} : ℕ := {BASE + k}')
E(f'def certRowCount : ℕ := {BASE + len(TABLE)}')
E('')
E('/-- The rows at `100 + k`, in index order. -/')
E('noncomputable def certExtraRows : List WRow := [')
E(',\n'.join(f'  ⟨{info[n]["m"]}, {n}B, lib_{n}⟩' for n in TABLE))
E(']')
E('')
E('/-- Sixty copies of the walk\'s first row fill indices `40 … 99` (room for the layout rows). -/')
E('noncomputable def padRows : List WRow := List.replicate 60 ⟨1, zeroLtSuccB, lib_zeroLtSucc⟩')
E('')
E('/-- The certification table\'s rows: the walk\'s, the pad, the extra rows. -/')
E('noncomputable def certTailRows : List WRow := padRows ++ certExtraRows')
E('noncomputable def certRows : List WRow := walkRows ++ certTailRows')
E('')
E('lemma certRows_length : certRows.length = certRowCount := rfl')
E('')
E('/-- **The certification proof table**: `certRowCount` rows at least, the `i`-th with the arity and the matrix')
E('of `certRows[i]`. -/')
E('def CertTable (tbl : V) : Prop :=')
E('  (certRowCount : V) ≤ len tbl ∧')
E('  ∀ (i : ℕ) (h : i < certRows.length),')
E('    rowM tbl.[(i : V)] = ((certRows[i]).m : V) ∧ rowB tbl.[(i : V)] = ⌜Semiformula.lMap emb (certRows[i]).B⌝')
E('')
E('/-- A certification table is a walk table (the first 40 rows). -/')
E('lemma CertTable.walkTable {tbl : V} (h : CertTable tbl) : WalkTable tbl := by')
E('  refine ⟨le_trans (by exact_mod_cast (by decide : walkRowCount ≤ certRowCount)) h.1, ?_⟩')
E('  intro i hi')
E('  have hi\' : i < certRows.length := by')
E('    rw [certRows_length]; exact lt_of_lt_of_le (walkRows_length ▸ hi) (by decide)')
E('  have := h.2 i hi\'')
E('  rwa [show certRows[i] = walkRows[i] from List.getElem_append_left hi] at this')
E('')
E('/-- **The certification proof table exists in every model, with one standard length bound.** -/')
E('theorem exists_certTable : ∃ N : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],')
E('    ∃ tbl : V, TableOK tbl (N : V) ∧ CertTable tbl := by')
E('  obtain ⟨N, hN⟩ := exists_rows certRows')
E('  refine ⟨N, fun V _ _ ↦ ?_⟩')
E('  obtain ⟨rows, hlen, hok, hidx⟩ := hN V')
E('  refine ⟨vecOf rows, tableOK_vecOf rows hok, ?_, ?_⟩')
E('  · rw [len_vecOf, hlen, certRows_length]')
E('  · intro i h')
E('    have h\' : i < rows.length := by rw [hlen]; exact h')
E('    rw [nth_vecOf rows i h\']')
E('    exact hidx i h h\'')
E('')
E('lemma certTable_len {tbl : V} (h : CertTable tbl) (i : ℕ) (hi : i < certRowCount) : ((i : ℕ) : V) < len tbl :=')
E('  lt_of_lt_of_le (by exact_mod_cast hi) h.1')
E('')
E('/-! ### The per-row readings of `CertTable` -/')
E('')
for name in TABLE:
    d = info[name]
    c = f'(^∃ row_{name}_R)' if d['tag2'] else f'row_{name}_c'
    E(f'lemma certTable_{name} {{tbl : V}} (h : CertTable tbl) :')
    E(f'    rowM tbl.[((cIdx_{name} : ℕ) : V)] = (({d["m"]} : ℕ) : V) ∧')
    E(f'    rowB tbl.[((cIdx_{name} : ℕ) : V)] = impChainV LAct (vecOf row_{name}_as) {c} := by')
    E(f'  have this : rowM tbl.[((cIdx_{name} : ℕ) : V)] = (({d["m"]} : ℕ) : V) ∧')
    E(f'      rowB tbl.[((cIdx_{name} : ℕ) : V)] = ⌜Semiformula.lMap emb {name}B⌝ :=')
    E(f'    h.2 cIdx_{name} (Nat.lt_of_sub_eq_succ rfl)')
    E(f'  refine ⟨this.1, ?_⟩')
    E(f'  rw [impChainV_vecOf, this.2, quote_row_{name}]')
    if d['tag2']:
        E('  rfl')
    E('')
E('/-! ### The piece table -/')
E('')
for name in TABLE:
    d = info[name]
    if d['tag2']:
        E(f'noncomputable def cpiece_{name} : V := ⟪(2 : V), vecOf row_{name}_as, row_{name}_R⟫')
    else:
        E(f'noncomputable def cpiece_{name} : V := ⟪(0 : V), vecOf row_{name}_as, row_{name}_c⟫')
E('')
E('noncomputable def certExtraPieceList : List V := [')
E(',\n'.join(f'  cpiece_{n}' for n in TABLE))
E(']')
E('noncomputable def padPieceList : List V := List.replicate 60 piece_zeroLtSucc')
E('')
E('/-- **The piece table of the certification producers**: the walk\'s pieces, the pad, the extra rows\' pieces. -/')
E('noncomputable def certTailPieceList : List V := padPieceList ++ certExtraPieceList')
E('noncomputable def certPieces : V := vecOf (walkPieceList ++ certTailPieceList)')
E('')
E('lemma certPieces_nth_lt (i : ℕ) (hi : i < walkRowCount) : (certPieces : V).[(i : V)] = (walkPieces : V).[(i : V)] := by')
E('  unfold certPieces walkPieces')
E('  have h1 : i < (walkPieceList ++ certTailPieceList : List V).length := by')
E('    rw [show (walkPieceList ++ certTailPieceList : List V).length = certRowCount from rfl]')
E('    exact lt_of_lt_of_le hi (by decide)')
E('  have h2 : i < (walkPieceList : List V).length := by')
E('    rw [show (walkPieceList : List V).length = walkRowCount from rfl]; exact hi')
E('  rw [nth_vecOf _ i h1, nth_vecOf _ i h2]')
E('  exact List.getElem_append_left h2')
E('')
E('/-- A walk step read from the certification pieces is the walk\'s step. -/')
E('lemma mkStep_certPieces_lt (i : ℕ) (hi : i < walkRowCount) (ev : V) :')
E('    mkStep certPieces (i : V) ev = mkStep walkPieces (i : V) ev := by')
E('  rw [mkStep, mkStep, certPieces_nth_lt i hi]')
E('')
for name in TABLE:
    d = info[name]
    idx = BASE + TABLE.index(name)
    E(f'lemma certPieces_{name} : (certPieces : V).[((cIdx_{name} : ℕ) : V)] = cpiece_{name} := by')
    E(f'  unfold certPieces')
    E(f'  rw [nth_vecOf _ cIdx_{name} (Nat.lt_of_sub_eq_succ rfl)]')
    E(f'  rfl')
    E('')
    if d['tag2']:
        E(f'lemma cmk_{name} (ev : V) :')
        E(f'    mkStep certPieces ((cIdx_{name} : ℕ) : V) ev = sIntroFact ((cIdx_{name} : ℕ) : V) ev (vecOf row_{name}_as) row_{name}_R := by')
        E(f'  rw [mkStep, certPieces_{name}]')
        E(f'  simp [cpiece_{name}, sIntroFact]')
        E('')
        E(f'lemma ctag_{name} {{W : V}} (hWp : W = certPieces) (ev : V) : sTag (mkStep W ({idx} : V) ev) = 2 := by')
        E(f'  subst hWp')
        E(f'  have hk : ((cIdx_{name} : ℕ) : V) = ({idx} : V) := by simp [cIdx_{name}]')
        E(f'  rw [← hk, cmk_{name}]; simp')
    else:
        E(f'lemma cmk_{name} (ev : V) :')
        E(f'    mkStep certPieces ((cIdx_{name} : ℕ) : V) ev = sUseHorn ((cIdx_{name} : ℕ) : V) ev (vecOf row_{name}_as) row_{name}_c := by')
        E(f'  rw [mkStep, certPieces_{name}]')
        E(f'  simp [cpiece_{name}, sUseHorn]')
        E('')
        E(f'lemma ctag_{name} {{W : V}} (hWp : W = certPieces) (ev : V) : sTag (mkStep W ({idx} : V) ev) = 0 := by')
        E(f'  subst hWp')
        E(f'  have hk : ((cIdx_{name} : ℕ) : V) = ({idx} : V) := by simp [cIdx_{name}]')
        E(f'  rw [← hk, cmk_{name}]; simp')
    E('')
E('/-! ### The per-row applicability lemmas `cok_<row>` -/')
E('')
for name in TABLE:
    d = info[name]
    idx = BASE + TABLE.index(name)
    ws = d['wits']; facts = d['facts']; conc = d['conc']
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
    inst_args = ' '.join(f'h{w}' for w in ws)
    tag = 2 if d['tag2'] else 0
    RM = 9 if name == 'tsvAdjCert' else 8
    if d['tag2']:
        after = f'insert (neg LAct (free LAct ({conc}))) (setShift LAct Γ)' if False else None
        # ctxAfter of an intro step: insert (neg (CONC)) (setShift Γ) where CONC = freeIter 1 (...) form
        after = f'insert (neg LAct ({conc})) (setShift LAct Γ)'
    else:
        after = f'insert (neg LAct ({conc})) Γ'
    E(f'/-- Row `{name}` as a step. -/')
    E(f'lemma cok_{name} {{tbl N E Γ W : V}} {binders}(htbl : TableOK tbl N) (hC : CertTable tbl) (hWp : W = certPieces)')
    E(f'    (hΓ : IsFormulaSet LAct Γ) {hyps} {mems} :')
    E(f'    StepOK tbl E (({RM} : ℕ) : V) Γ (mkStep W {idx} {vec}) ∧ sTag (mkStep W {idx} {vec}) = {tag} ∧')
    E(f'    ctxAfter Γ (mkStep W {idx} {vec}) = {after} := by')
    E(f'  subst hWp')
    E(f'  have hk : ((cIdx_{name} : ℕ) : V) = ({idx} : V) := by simp [cIdx_{name}]')
    E(f'  have hstep := cmk_{name} (V := V) {vec}')
    E(f'  have hlen := certTable_len hC cIdx_{name} (by decide)')
    E(f'  have hrow := certTable_{name} hC')
    E(f'  rw [hk] at hstep hlen hrow')
    E(f'  have hes : ∀ e ∈ {lst}, IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := {hes_term}')
    E(f'  have hinst := inst_{name} {inst_args}')
    E(f'  rw [hstep, show ({vec} : V) = vecOf {lst} from rfl]')
    if d['tag2']:
        E(f'  refine ⟨stepOK_introFact htbl {lst} row_{name}_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : {len(ws)} ≤ {RM}))')
        E(f'    (by rw [show row_{name}_as.length = {len(facts)} from rfl]; exact_mod_cast (by decide : {len(facts)} ≤ {RM})) hes ?_, by simp, ?_⟩')
        E(f'  · exact neg_mem_of_map hinst.1 ({mem_term})')
        E(f'  · rw [ctxAfter_introFact {lst} row_{name}_as (by rw [← Nat.cast_succ]; exact isSemiformula_{name}_R) (fun e he ↦ (hes e he).1),')
        E(f'      show row_{name}_R = row_{name}_body from rfl, ← freeIter_one, hinst.2]')
    else:
        E(f'  refine ⟨stepOK_useHorn htbl {lst} row_{name}_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : {len(ws)} ≤ {RM}))')
        E(f'    (by rw [show row_{name}_as.length = {len(facts)} from rfl]; exact_mod_cast (by decide : {len(facts)} ≤ {RM})) hes ?_, by simp, ?_⟩')
        E(f'  · exact neg_mem_of_map hinst.1 ({mem_term})')
        E(f'  · rw [ctxAfter_useHorn {lst} row_{name}_as isSemiformula_{name}_c (fun e he ↦ (hes e he).1), hinst.2]')
    E('')
E('end certTable')

head = '''import ArithS.Necessitation.Describe
import ArithS.Necessitation.RowInstB

/-!
# ArithS.Necessitation.CertRows — the certification table (GENERATED by `arith/scripts/gen_cert.py`)

1. The ten `Lib/Lengths.lean` rows the length producer uses (`formulaLen{Verum,Falsum,And,Or,All,Exs}`,
   `termLen{Bvar,Fvar}`, `formulaLenTotal`, `termLenTotal`) re-issued with their `quote_row_`/`inst_` lemmas
   (blocks produced by `gen_frag.py`'s `gen_row`; the originals in `Lengths.lean` have none, and the shared
   generated files are left untouched).
2. The certification table: `certRows := walkRows ++ padRows ++ certExtraRows` — the 40 walk rows at their
   indices, a pad of 60 copies of the walk's first row (indices `40 … 99`, room for the layout rows), then the
   rows of `Cert.lean` at `cIdx_<row> = 100 + k` (certification `neg/shift/subst/free` and the term-level rows,
   the identification rows `eqOf*`/`eqRefl/eqSymm/eqTrans`, `congRel/congNRel`, the length rows). `CertTable tbl`
   (implies `WalkTable tbl`), `exists_certTable`, the piece table `certPieces` extending `walkPieces` entrywise
   (`mkStep_certPieces_lt`), and per row `certTable_<row>`, `cmk_<row>`, `ctag_<row>`, `cok_<row>` (the step is
   applicable at its own `M` and its `ctxAfter` inserts the canonical fact).

**The `M` convention.** Every `cok_<row>` is stated at the row's OWN minimal cost cap: `M = 8` for all rows
but one, and `M = 9` for `cIdx_tsvAdjCert` (the term-substitution vector-adjoin step, 9 witnesses — it is IN
the table since 2026-09-14, at the last index; the earlier note that the `M = 8` cap excluded it was wrong,
the cap is per-consumer, not per-table). A consumer that mixes `tsvAdjCert` with `M = 8` siblings runs the
whole pass at `M = 9` and lifts the siblings with `Frag1.lean`'s `StepOK.mono`/`ListOK.mono`
(`h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V)`) — exactly the idiom `Frag2.lean`'s `nodeExs` already uses for the
arity-9 `introExs` row. Stating the `M = 8` rows at 9 directly was rejected: it would weaken every existing
consumer that is happy at 8, and `.mono` is a one-line lift at the single mixing site.

A second blocker reported against `Cert.lean` — that `lenSteps` is blocked because `Describe.lean`'s `NoDrop`
excludes tags 6/7 — is a NON-ISSUE: `Frag1.lean:21` already defines `NoDrop'` (tags 0–4, 6, 7) with
`noDrop'_appendV`, `noDrop'_cons`, `mem_ctxVec_of_mem'`, `mem_finalCtx_of_mem'` and the coercion
`NoDrop.noDrop'`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 20000

/-! ## 0. Three rows APPENDED 2026-09-14 for `lenSteps` (hand-written sentences and `lib_` proofs; their
`quote_row_`/`inst_` blocks are generated below like the length rows): the addition congruence `congAdd`
(`x = x' → y = y' → x + y = x' + y'`), the successor congruence `congSucc` (`x = x' → x + 1 = x' + 1` — the
one `lenSteps` uses: the closed `bnum|p| + bnum|q| + 1 = bnum(|p| + |q| + 1)` is `addFact` + `congSucc` +
`succFact` + `eqTrans`; `congAdd` at `𝟏` would need the closed-constant witness), and the INTRO form of the
list-sum adjoin `listSumAdjI` (`listSumDef s M → adjoinDef M' l M → l + s = s' → listSumDef s' M'` — the table's
`listSumAdj` has all three `listSumDef` facts as antecedents, so no `listSumDef s' M'` was derivable for a
non-empty `M'`; the intro form takes the sum as a NUMERAL via `addFact`, no `listSumTotal` eigenvariable). -/

section newRows

/-- `x = x' → y = y' → x + y = x' + y'`. -/
noncomputable def congAddB : ArithmeticSemisentence 4 :=
  “y' y x' x. x = x' → y = y' → (x + y) = (x' + y')”
noncomputable def congAdd : ArithmeticSentence := ∀¹* congAddB
lemma models_congAdd : V↓[ℒₒᵣ] ⊧ congAdd ↔ ∀ y' y x' x : V, x = x' → y = y' → x + y = x' + y' := by
  simp [congAdd, congAddB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congAdd : 𝗣𝗔 ⊢ congAdd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congAdd.mpr fun _ _ _ _ h₁ h₂ ↦ by subst h₁; subst h₂; rfl
theorem lib_congAdd : Lib congAdd := Lib.of_pa pa_proves_congAdd

/-- `x = x' → x + 1 = x' + 1`. -/
noncomputable def congSuccB : ArithmeticSemisentence 2 :=
  “x' x. x = x' → (x + 1) = (x' + 1)”
noncomputable def congSucc : ArithmeticSentence := ∀¹* congSuccB
lemma models_congSucc : V↓[ℒₒᵣ] ⊧ congSucc ↔ ∀ x' x : V, x = x' → x + 1 = x' + 1 := by
  simp [congSucc, congSuccB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congSucc : 𝗣𝗔 ⊢ congSucc :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congSucc.mpr fun _ _ h ↦ by subst h; rfl
theorem lib_congSucc : Lib congSucc := Lib.of_pa pa_proves_congSucc

/-- `listSum M = s → M' = l ∷ M → l + s = s' → listSum M' = s'` (the intro form of `listSumAdj`). -/
noncomputable def listSumAdjIB : ArithmeticSemisentence 5 :=
  “s' s l M M'. !listSumDef s M → !adjoinDef M' l M → (l + s) = s' → !listSumDef s' M'”
noncomputable def listSumAdjI : ArithmeticSentence := ∀¹* listSumAdjIB
lemma models_listSumAdjI : V↓[ℒₒᵣ] ⊧ listSumAdjI ↔
    ∀ s' s l M M' : V, s = listSum M → M' = l ∷ M → l + s = s' → s' = listSum M' := by
  simp [listSumAdjI, listSumAdjIB, models_iff, Matrix.vecForall_iff, listSum_defined.iff]
theorem pa_proves_listSumAdjI : 𝗣𝗔 ⊢ listSumAdjI :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_listSumAdjI.mpr fun _ _ _ _ _ h₁ h₂ h₃ ↦ by
    subst h₁; subst h₂; subst h₃; simp
theorem lib_listSumAdjI : Lib listSumAdjI := Lib.of_pa pa_proves_listSumAdjI

/-- `e' = e → e = termSubst w t → e' = termSubst w t` (the term-level twin of `congSubstL`; APPENDED
2026-09-14 for `certSubst`'s bound-variable leaf: `termSubstBvarCert` is applied at the ORIGINAL entry of
the substitution vector, the image leaf is identified with it, and this row moves the fact onto the image). -/
noncomputable def congTSubstLB : ArithmeticSemisentence 4 :=
  “t w e' e. e' = e → !(termSubstGraph LAct) e w t → !(termSubstGraph LAct) e' w t”
noncomputable def congTSubstL : ArithmeticSentence := ∀¹* congTSubstLB
lemma models_congTSubstL : V↓[ℒₒᵣ] ⊧ congTSubstL ↔
    ∀ t w e' e : V, e' = e → e = termSubst LAct w t → e' = termSubst LAct w t := by
  simp [congTSubstL, congTSubstLB, models_iff, Matrix.vecForall_iff, termSubst.defined.iff]
theorem pa_proves_congTSubstL : 𝗣𝗔 ⊢ congTSubstL :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congTSubstL.mpr fun _ _ _ _ h₁ h₂ ↦ by subst h₁; exact h₂
theorem lib_congTSubstL : Lib congTSubstL := Lib.of_pa pa_proves_congTSubstL

end newRows

/-! ## 1. The length rows, re-issued (+ the three new rows' generated blocks) -/

section lengthRows

'''
open('ArithS/Necessitation/CertRows.lean','w').write(head + len_blocks + '\nend lengthRows\n\n' + '\n'.join(o) + '\n\nend ArithS\n')
print('rows', len(TABLE))
