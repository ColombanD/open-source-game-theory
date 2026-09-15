"""gen_prologue.py — generates arith/ArithS/Necessitation/PrologueRows.lean (2026-09-14):
the rows the PROLOGUE producers (`Prologue.lean`) need beyond the top table, on the `gen_frag2.py`
template — currently ONE row, `setLenSingLe` (`setLen (insert x ∅) ≤ |x|`, the base of the `setLen`
fold of `DESIGN_fragments.md` §3.4), with its `Lib` block (`gen_frag.py`'s `gen_frag_row`), its
`quote_row_`/`inst_` block (`gen_row`), the extra rows `proExtraRows` at `pIdx_<row> = topRowCount + k`
(APPEND-ONLY: never reorder), the piece table `proPieces` extending `topPieces` entrywise
(`mkStep_proPieces_lt`), and per row `pmk_<row>`, `ptag_<row>`, `pok_<row>` — the latter stated against
EXPLICIT table-reading hypotheses (`hlen`, `hrow`), so that the generated file knows no table predicate
(`ProTable` lives in `Prologue.lean`, which also carries the certification tail).
Run from arith/: python3 scripts/gen_prologue.py
"""
import sys, re, os, types
HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, 'gen_frag.py')).read()
_src = _src[:_src.index('\ngen_frag()\ngen_rowinstb()')].replace("if len(sys.argv) > 3:", "if False:")
G = types.ModuleType('genfrag_lib')
G.__file__ = os.path.join(HERE, 'gen_frag.py')
exec(compile(_src, G.__file__, 'exec'), G.__dict__)
A, EX, S, P, C, by = G.A, G.EX, G.S, G.P, G.C, G.by

# ---- the new rows: (name, binders, ants, conc, proof, doc)
NEW_ROWS = [
 ('setLenSingLe', ['lx', 'l', 't', 'x'],
  [A('insert', 't', 'x', 'Z'), A('setLen', 'l', 't'), A('flenG', 'lx', 'x')], A('le', 'l', 'lx'),
  by("subst_vars; rw [setLen_insert_of_not_mem_V (L := LAct) (by simp), ← emptyset_def, setLen_empty, zero_add]"),
  '`t = insert x ∅ → l = setLen t → lx = |x| → l ≤ lx` (the base of the `setLen` fold: a singleton is at most its member).'),
 ('setLenEmptyLe', ['l'],
  [A('setLen', 'l', 'Z')], A('le', 'l', 'Z'),
  by("subst_vars; rw [← emptyset_def, setLen_empty]; try exact le_refl _"),
  '`l = setLen ∅ → l ≤ 0` (the empty sequent: its length object is bounded by the numeral `bnum 0 = 𝟎`).'),
]
# Rows whose `Lib` block AND `quote_row_`/`inst_` block already exist (`Lib/Frag.lean`, `RowInstB.lean`) but which sit
# in no piece table: only their table entries are generated here (APPEND-ONLY).
EXISTING_ROWS = ['congSubsetL', 'congSetShiftR']

G.frag = []
G.out = []
for (name, binders, ants, conc, proof, doc) in NEW_ROWS:
    G.gen_frag_row('pro', name, binders, ants, conc, proof, doc)
    G.gen_row(name, binders, ants, conc)
lib_blocks = '\n'.join(G.frag)
new_blocks = '\n'.join(G.out)

TABLE = [n for (n, *_r) in NEW_ROWS] + EXISTING_ROWS
BASE = 155
alltext = new_blocks + open(os.path.join(HERE, '..', 'ArithS', 'Necessitation', 'RowInstB.lean')).read()

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
E('/-! ## 2. The extra rows at `topRowCount + k`, the piece table, the applicability lemmas -/')
E('')
E('section proRowsTable')
E('')
for k, name in enumerate(TABLE):
    E(f'def pIdx_{name} : ℕ := {BASE + k}')
E(f'def proExtraRowCount : ℕ := {len(TABLE)}')
E('')
E('/-- The extra rows at `topRowCount + k`, in index order (append-only). -/')
E('noncomputable def proExtraRows : List WRow := [')
E(',\n'.join(f'  ⟨{info[n]["m"]}, {n}B, lib_{n}⟩' for n in TABLE))
E(']')
E('')
E('lemma proExtraRows_length : proExtraRows.length = proExtraRowCount := rfl')
E('')
E('/-! ### The piece table -/')
E('')
for name in TABLE:
    d = info[name]
    if d['tag2']:
        E(f'noncomputable def ppiece_{name} : V := ⟪(2 : V), vecOf row_{name}_as, row_{name}_R⟫')
    else:
        E(f'noncomputable def ppiece_{name} : V := ⟪(0 : V), vecOf row_{name}_as, row_{name}_c⟫')
E('')
E('noncomputable def proExtraPieceList : List V := [')
E(',\n'.join(f'  ppiece_{n}' for n in TABLE))
E(']')
E('')
E("/-- **The piece table of the prologue producers**: the top's pieces, then the extra rows' pieces. -/")
E('noncomputable def proPieces : V := vecOf (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList ++ topExtraPieceList ++ proExtraPieceList)')
E('')
E('lemma proPieces_nth_lt (i : ℕ) (hi : i < topRowCount) : (proPieces : V).[(i : V)] = (topPieces : V).[(i : V)] := by')
E('  unfold proPieces topPieces')
E('  have h1 : i < (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList ++ topExtraPieceList ++ proExtraPieceList : List V).length := by')
E('    rw [show (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList ++ topExtraPieceList ++ proExtraPieceList : List V).length = topRowCount + proExtraRowCount from rfl]')
E('    exact lt_of_lt_of_le hi (Nat.le_add_right _ _)')
E('  have h2 : i < (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList ++ topExtraPieceList : List V).length := by')
E('    rw [show (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList ++ topExtraPieceList : List V).length = topRowCount from rfl]; exact hi')
E('  rw [nth_vecOf _ i h1, nth_vecOf _ i h2]')
E('  exact List.getElem_append_left h2')
E('')
E("/-- A top step read from the prologue pieces is the top's step. -/")
E('lemma mkStep_proPieces_lt (i : ℕ) (hi : i < topRowCount) (ev : V) :')
E('    mkStep proPieces (i : V) ev = mkStep topPieces (i : V) ev := by')
E('  rw [mkStep, mkStep, proPieces_nth_lt i hi]')
E('')
for name in TABLE:
    d = info[name]
    idx = BASE + TABLE.index(name)
    E(f'lemma proPieces_{name} : (proPieces : V).[((pIdx_{name} : ℕ) : V)] = ppiece_{name} := by')
    E(f'  unfold proPieces')
    E(f'  rw [nth_vecOf _ pIdx_{name} (Nat.lt_of_sub_eq_succ rfl)]')
    E(f'  rfl')
    E('')
    if d['tag2']:
        E(f'lemma pmk_{name} (ev : V) :')
        E(f'    mkStep proPieces ((pIdx_{name} : ℕ) : V) ev = sIntroFact ((pIdx_{name} : ℕ) : V) ev (vecOf row_{name}_as) row_{name}_R := by')
        E(f'  rw [mkStep, proPieces_{name}]')
        E(f'  simp [ppiece_{name}, sIntroFact]')
        E('')
        E(f'lemma ptag_{name} {{W : V}} (hWp : W = proPieces) (ev : V) : sTag (mkStep W ({idx} : V) ev) = 2 := by')
        E(f'  subst hWp')
        E(f'  have hk : ((pIdx_{name} : ℕ) : V) = ({idx} : V) := by simp [pIdx_{name}]')
        E(f'  rw [← hk, pmk_{name}]; simp')
    else:
        E(f'lemma pmk_{name} (ev : V) :')
        E(f'    mkStep proPieces ((pIdx_{name} : ℕ) : V) ev = sUseHorn ((pIdx_{name} : ℕ) : V) ev (vecOf row_{name}_as) row_{name}_c := by')
        E(f'  rw [mkStep, proPieces_{name}]')
        E(f'  simp [ppiece_{name}, sUseHorn]')
        E('')
        E(f'lemma ptag_{name} {{W : V}} (hWp : W = proPieces) (ev : V) : sTag (mkStep W ({idx} : V) ev) = 0 := by')
        E(f'  subst hWp')
        E(f'  have hk : ((pIdx_{name} : ℕ) : V) = ({idx} : V) := by simp [pIdx_{name}]')
        E(f'  rw [← hk, pmk_{name}]; simp')
    E('')
E('/-! ### The per-row applicability lemmas `pok_<row>` (against explicit table readings) -/')
E('')
for name in TABLE:
    d = info[name]
    idx = BASE + TABLE.index(name)
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
    inst_args = ' '.join(f'h{w}' for w in ws)
    tag = 2 if d['tag2'] else 0
    c = f'(^∃ row_{name}_R)' if d['tag2'] else f'row_{name}_c'
    if d['tag2']:
        after = f'insert (neg LAct ({conc})) (setShift LAct Γ)'
    else:
        after = f'insert (neg LAct ({conc})) Γ'
    E(f'/-- Row `{name}` as a step, against the table readings `hlen`/`hrow` at its index. -/')
    E(f'lemma pok_{name} {{tbl N E Γ W : V}} {binders}(htbl : TableOK tbl N) (hWp : W = proPieces)')
    E(f'    (hlen : ((pIdx_{name} : ℕ) : V) < len tbl)')
    E(f'    (hrow : rowM tbl.[((pIdx_{name} : ℕ) : V)] = (({d["m"]} : ℕ) : V) ∧')
    E(f'      rowB tbl.[((pIdx_{name} : ℕ) : V)] = impChainV LAct (vecOf row_{name}_as) {c})')
    E(f'    (hΓ : IsFormulaSet LAct Γ) {hyps} {mems} :')
    E(f'    StepOK tbl E (({Mcap} : ℕ) : V) Γ (mkStep W {idx} {vec}) ∧ sTag (mkStep W {idx} {vec}) = {tag} ∧')
    E(f'    ctxAfter Γ (mkStep W {idx} {vec}) = {after} := by')
    E(f'  subst hWp')
    E(f'  have hk : ((pIdx_{name} : ℕ) : V) = ({idx} : V) := by simp [pIdx_{name}]')
    E(f'  have hstep := pmk_{name} (V := V) {vec}')
    E(f'  rw [hk] at hstep hlen hrow')
    E(f'  have hes : ∀ e ∈ {lst}, IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := {hes_term}')
    E(f'  have hinst := inst_{name} {inst_args}')
    E(f'  rw [hstep, show ({vec} : V) = vecOf {lst} from rfl]')
    if d['tag2']:
        E(f'  refine ⟨stepOK_introFact htbl {lst} row_{name}_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : {len(ws)} ≤ {Mcap}))')
        E(f'    (by rw [show row_{name}_as.length = {len(facts)} from rfl] <;> exact_mod_cast (by decide : {len(facts)} ≤ {Mcap})) hes ?_, by simp, ?_⟩')
        E(f'  · exact neg_mem_of_map hinst.1 ({mem_term})')
        E(f'  · rw [ctxAfter_introFact {lst} row_{name}_as (by rw [← Nat.cast_succ]; exact isSemiformula_{name}_R) (fun e he ↦ (hes e he).1),')
        E(f'      show row_{name}_R = row_{name}_body from rfl, ← freeIter_one, hinst.2]')
    else:
        E(f'  refine ⟨stepOK_useHorn htbl {lst} row_{name}_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : {len(ws)} ≤ {Mcap}))')
        E(f'    (by rw [show row_{name}_as.length = {len(facts)} from rfl] <;> exact_mod_cast (by decide : {len(facts)} ≤ {Mcap})) hes ?_, by simp, ?_⟩')
        E(f'  · exact neg_mem_of_map hinst.1 ({mem_term})')
        E(f'  · rw [ctxAfter_useHorn {lst} row_{name}_as isSemiformula_{name}_c (fun e he ↦ (hes e he).1), hinst.2]')
    E('')
E('end proRowsTable')

head = '''import ArithS.Necessitation.Top

/-!
# ArithS.Necessitation.PrologueRows — the prologue rows (GENERATED by `arith/scripts/gen_prologue.py`)

The rows `Prologue.lean` needs beyond the top table, each with its `Lib` block (`<row>B`, `models_`,
`pa_proves_`, `lib_`) and its `quote_row_`/`inst_` block; the extra rows `proExtraRows` at
`pIdx_<row> = topRowCount + k` (APPEND-ONLY, index-stable); the piece table `proPieces` extending
`topPieces` entrywise (`mkStep_proPieces_lt`); per row `pmk_<row>`, `ptag_<row>`, `pok_<row>`.
The applicability lemmas take the table readings at the row's index as EXPLICIT hypotheses — no table
predicate is defined here (`Prologue.lean`'s `ProTable` places these rows and the certification tail).

Currently: `setLenSingLe` (155) — `t = insert x ∅ → l = setLen t → lx = |x| → l ≤ lx`, the base of the
`setLen` fold (`DESIGN_fragments.md` §3.4; the library's `setLenInsertLe` needs a length object of the
set below, and the empty set has none in any table); `setLenEmptyLe` (156) — `l = setLen ∅ → l ≤ 0`, the
EMPTY sequent's layout; and two library rows that were in no piece table, `congSubsetL` (157) and
`congSetShiftR` (158) (their `Lib` and `inst_` blocks live in `Lib/Frag.lean` / `RowInstB.lean`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 20000

/-! ## 0. The library rows (`Lib`) -/

section proLib

'''
mid = '''
end proLib

/-! ## 1. The rows as pieces: `row_<r>_as`/`_c`, `quote_row_<r>`, `inst_<r>` (the `RowInstB` template) -/

section proRowInst

'''
tail = '''
end proRowInst

'''
text = head + lib_blocks + mid + new_blocks + tail + '\n'.join(o) + '\n\nend ArithS\n'
open(os.path.join(HERE, '..', 'ArithS', 'Necessitation', 'PrologueRows.lean'), 'w').write(text)
print('wrote PrologueRows.lean', len(text.splitlines()), 'lines')
