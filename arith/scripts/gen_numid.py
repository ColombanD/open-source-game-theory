"""gen_numid.py — generates arith/ArithS/Necessitation/NumIdRows.lean (2026-09-15):
the rows the PIN (`Pin.lean`, `DESIGN_fragments.md` §7.1 steps 1–4) needs beyond the prologue table, on the
`gen_prologue.py` template: the five EXISTING library rows `instBIntro`, `congSubstArg`, `bnumZeroCert`,
`bnumOneCert`, `bnumEvenCert` (their `Lib`/`quote_row_`/`inst_` blocks live in `Lib/Frag.lean`/`RowInstB.lean`
— only the TABLE part is generated for them) and ONE new row `bnumOddOfEven` (the odd bit-step through the
even numeral: `bnumOddCert` has 12 witnesses and cannot run under the cap `M = 9`), placed at
`nIdx_<row> = proRowCount + k` (APPEND-ONLY after the prologue table, SYMBOLIC in `proRowCount` so a prologue
row appended concurrently moves nothing but the base), the piece table `numIdPieces` extending `proPieces`
entrywise (a zero pad over the certification tail, which has no pieces), and per row `nmk_`/`ntag_`/`nok_`
stated against EXPLICIT table readings (`hlen`, `hrow`) — `NumIdTable` lives in `Pin.lean`.
Run from arith/: python3 scripts/gen_numid.py
"""
import sys, re, os, types
HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, 'gen_frag.py')).read()
_src = _src[:_src.index('\ngen_frag()\ngen_rowinstb()')].replace("if len(sys.argv) > 3:", "if False:")
G = types.ModuleType('genfrag_lib')
G.__file__ = os.path.join(HERE, 'gen_frag.py')
exec(compile(_src, G.__file__, 'exec'), G.__dict__)
A, EX, S, P, C, M, by = G.A, G.EX, G.S, G.P, G.C, G.M, G.by

EXISTING = ['instBIntro', 'congSubstArg', 'bnumZeroCert', 'bnumOneCert', 'bnumEvenCert']
NEW_ROWS = [
 ('bnumOddOfEven', ['u', 'x', "x'", 's', 'one', 'm'],
  [A('le', 'One', 'm'), A('bnumG', 's', M('Two', 'm')), A('qqFunc', 'one', 'Z', C(1), 'Z'), A('adjoin', "x'", 'one', 'Z'),
   A('adjoin', 'x', 's', "x'"), A('qqFunc', 'u', C(2), 'Z', 'x')],
  A('bnumG', 'u', P(M('Two', 'm'), 'One')),
  by('subst_vars; rw [bnum_two_mul_add_one h₁, ← bnum_two_mul h₁]; simp only [qqAdd, coe_addIndex_eq, Arithmetic.one, qqFuncN_eq_qqFunc, qqFunc_absolute, coe_oneIndex_eq, Nat.cast_zero, zero_add, one_add_one_eq_two]'),
  "`1 ≤ m → s = bnum (2 * m) → u = s ^+ 𝟏 (as `func`/`∷` facts) → u = bnum (2 * m + 1)` — the odd bit-step THROUGH the even numeral (`bnumOddCert` has 12 witnesses, above the cap `M = 9`)."),
]
TABLE = EXISTING + [n for (n, *_r) in NEW_ROWS]

specs = {r[1]: r for r in G.ROWS}
# info for all six rows: generate the row blocks into a scratch buffer, keep only the NEW row's text
G.frag = []; G.out = []
for name in EXISTING:
    (_g, _n, binders, ants, conc, _p, _d) = specs[name]
    G.gen_row(name, binders, ants, conc)
existing_text = '\n'.join(G.out)
G.frag = []; G.out = []
for (name, binders, ants, conc, proof, doc) in NEW_ROWS:
    G.gen_frag_row('numid', name, binders, ants, conc, proof, doc)
    G.gen_row(name, binders, ants, conc)
lib_blocks = '\n'.join(G.frag)
new_blocks = '\n'.join(G.out)
alltext = existing_text + '\n' + new_blocks

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
    cm = re.search(r'instOuter LAct \[[^\]]*\] row_%s_c = (.*)$' % name, stmt, re.S)
    conc = ' '.join(cm.group(1).split())
    assert len(wits) == ar, (name, wits, ar)
    assert not tag2
    info[name] = dict(m=ar, wits=wits, facts=facts, conc=conc)

o = []
E = o.append
E('/-! ## 2. The extra rows at `proRowCount + k`, the piece table, the applicability lemmas -/')
E('')
E('section numIdRowsTable')
E('')
for k, name in enumerate(TABLE):
    E(f'def nIdx_{name} : ℕ := proRowCount + {k}')
E(f'def numIdExtraRowCount : ℕ := {len(TABLE)}')
E('')
E('/-- The extra rows at `proRowCount + k`, in index order (append-only). -/')
E('noncomputable def numIdExtraRows : List WRow := [')
E(',\n'.join(f'  ⟨{info[n]["m"]}, {n}B, lib_{n}⟩' for n in TABLE))
E(']')
E('')
E('lemma numIdExtraRows_length : numIdExtraRows.length = numIdExtraRowCount := rfl')
E('')
E('/-- **The pin table\'s rows**: the prologue rows, then the pin\'s rows. -/')
E('noncomputable def numIdRows : List WRow := proRows ++ numIdExtraRows')
E('def numIdRowCount : ℕ := proRowCount + numIdExtraRowCount')
E('lemma numIdRows_length : numIdRows.length = numIdRowCount := by')
E('  simp only [numIdRows, List.length_append, proRows_length, numIdExtraRows_length, numIdRowCount]')
E('')
E('/-! ### The piece table -/')
E('')
for name in TABLE:
    E(f'noncomputable def npiece_{name} : V := ⟪(0 : V), vecOf row_{name}_as, row_{name}_c⟫')
E('')
E('noncomputable def numIdExtraPieceList : List V := [')
E(',\n'.join(f'  npiece_{n}' for n in TABLE))
E(']')
E('')
E('/-- A zero pad over the certification tail (whose rows are used only through re-indexed lists and have no pieces). -/')
E('noncomputable def numIdPadPieceList : List V := List.replicate (certRowCount - walkRowCount) (0 : V)')
E('')
E("/-- **The piece table of the pin**: the prologue's pieces, the pad, then the extra rows' pieces. -/")
E('noncomputable def numIdPieces : V := vecOf (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList ++ topExtraPieceList ++ proExtraPieceList ++ numIdPadPieceList ++ numIdExtraPieceList)')
E('')
E('lemma numIdPieces_nth_lt (i : ℕ) (hi : i < proBase) : (numIdPieces : V).[(i : V)] = (proPieces : V).[(i : V)] := by')
E('  unfold numIdPieces proPieces')
E('  have h1 : i < (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList ++ topExtraPieceList ++ proExtraPieceList ++ numIdPadPieceList ++ numIdExtraPieceList : List V).length := by')
E('    rw [show (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList ++ topExtraPieceList ++ proExtraPieceList ++ numIdPadPieceList ++ numIdExtraPieceList : List V).length = numIdRowCount from rfl]')
E('    exact lt_of_lt_of_le hi (by simp only [numIdRowCount, proRowCount]; omega)')
E('  have h2 : i < (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList ++ topExtraPieceList ++ proExtraPieceList : List V).length := by')
E('    rw [show (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList ++ topExtraPieceList ++ proExtraPieceList : List V).length = proBase from rfl]; exact hi')
E('  have h3 : i < (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList ++ topExtraPieceList ++ proExtraPieceList ++ numIdPadPieceList : List V).length := by')
E('    rw [List.length_append]; exact lt_of_lt_of_le h2 (Nat.le_add_right _ _)')
E('  rw [nth_vecOf _ i h1, nth_vecOf _ i h2]')
E('  exact (List.getElem_append_left h3).trans (List.getElem_append_left h2)')
E('')
E("/-- A prologue step read from the pin's pieces is the prologue's step. -/")
E('lemma mkStep_numIdPieces_lt (i : ℕ) (hi : i < proBase) (ev : V) :')
E('    mkStep numIdPieces (i : V) ev = mkStep proPieces (i : V) ev := by')
E('  rw [mkStep, mkStep, numIdPieces_nth_lt i hi]')
E('')
for name in TABLE:
    E(f'lemma numIdPieces_{name} : (numIdPieces : V).[((nIdx_{name} : ℕ) : V)] = npiece_{name} := by')
    E(f'  unfold numIdPieces')
    E(f'  rw [nth_vecOf _ nIdx_{name} (Nat.lt_of_sub_eq_succ rfl)]')
    E(f'  rfl')
    E('')
    E(f'lemma nmk_{name} (ev : V) :')
    E(f'    mkStep numIdPieces ((nIdx_{name} : ℕ) : V) ev = sUseHorn ((nIdx_{name} : ℕ) : V) ev (vecOf row_{name}_as) row_{name}_c := by')
    E(f'  rw [mkStep, numIdPieces_{name}]')
    E(f'  simp [npiece_{name}, sUseHorn]')
    E('')
    E(f'lemma ntag_{name} {{W : V}} (hWp : W = numIdPieces) (ev : V) : sTag (mkStep W ((nIdx_{name} : ℕ) : V) ev) = 0 := by')
    E(f'  subst hWp')
    E(f'  rw [nmk_{name}]; simp')
    E('')
E('/-! ### The per-row applicability lemmas `nok_<row>` (against explicit table readings) -/')
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
    inst_args = ' '.join(f'h{w}' for w in ws)
    idx = f'((nIdx_{name} : ℕ) : V)'
    E(f'/-- Row `{name}` as a step, against the table readings `hlen`/`hrow` at its index. -/')
    E(f'lemma nok_{name} {{tbl N E Γ W : V}} {binders}(htbl : TableOK tbl N) (hWp : W = numIdPieces)')
    E(f'    (hlen : {idx} < len tbl)')
    E(f'    (hrow : rowM tbl.[{idx}] = (({d["m"]} : ℕ) : V) ∧')
    E(f'      rowB tbl.[{idx}] = impChainV LAct (vecOf row_{name}_as) row_{name}_c)')
    E(f'    (hΓ : IsFormulaSet LAct Γ) {hyps} {mems} :')
    E(f'    StepOK tbl E (({Mcap} : ℕ) : V) Γ (mkStep W {idx} {vec}) ∧ sTag (mkStep W {idx} {vec}) = 0 ∧')
    E(f'    ctxAfter Γ (mkStep W {idx} {vec}) = insert (neg LAct ({conc})) Γ := by')
    E(f'  subst hWp')
    E(f'  have hstep := nmk_{name} (V := V) {vec}')
    E(f'  have hes : ∀ e ∈ {lst}, IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := {hes_term}')
    E(f'  have hinst := inst_{name} {inst_args}')
    E(f'  rw [hstep, show ({vec} : V) = vecOf {lst} from rfl]')
    E(f'  refine ⟨stepOK_useHorn htbl {lst} row_{name}_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : {len(ws)} ≤ {Mcap}))')
    E(f'    (by rw [show row_{name}_as.length = {len(facts)} from rfl] <;> exact_mod_cast (by decide : {len(facts)} ≤ {Mcap})) hes ?_, by simp, ?_⟩')
    E(f'  · exact neg_mem_of_map hinst.1 ({mem_term})')
    E(f'  · rw [ctxAfter_useHorn {lst} row_{name}_as isSemiformula_{name}_c (fun e he ↦ (hes e he).1), hinst.2]')
    E('')
E('end numIdRowsTable')
table_part = '\n'.join(o)

header = '''import ArithS.Necessitation.Prologue

/-!
# ArithS.Necessitation.NumIdRows — the pin's rows (GENERATED by `arith/scripts/gen_numid.py`)

The rows `Pin.lean` needs beyond the prologue table (`DESIGN_fragments.md` §7.1 steps 1–4): the EXISTING
library rows `instBIntro`, `congSubstArg`, `bnumZeroCert`, `bnumOneCert`, `bnumEvenCert` (their `Lib`,
`quote_row_` and `inst_` blocks are in `Lib/Frag.lean` and `RowInstB.lean`; none of them was in any table) and
ONE new row `bnumOddOfEven` — the odd bit-step `1 ≤ m → s = bnum (2m) → u = s ^+ 𝟏 → u = bnum (2m + 1)`
through the even numeral (`bnumOddCert` has 12 witnesses and 12 antecedents, above the cap `M = 9` every
`ListOK` of the pin runs at; with `bnumEvenCert` (9 witnesses, cap 9) it covers every bit). The extra rows
`numIdExtraRows` sit at `nIdx_<row> = proRowCount + k` — APPEND-ONLY after the prologue table and SYMBOLIC
in `proRowCount`, so a prologue row appended concurrently moves only the base; the piece table `numIdPieces`
extends `proPieces` entrywise with a zero pad over the certification tail (whose rows have no pieces, being
used only through `reidxL`); per row `nmk_<row>`, `ntag_<row>`, `nok_<row>` — the applicability lemmas take
the table readings at the row's index as EXPLICIT hypotheses; `NumIdTable` lives in `Pin.lean`.
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

/-! ## 0. The new library row (`Lib`) -/

section numIdLib

'''
mid = '''
end numIdLib

/-! ## 1. Its `quote_row_`/`inst_` block (the `RowInstB` template) -/

section numIdRowInst

'''
mid2 = '''
end numIdRowInst

'''
footer = '''

end ArithS
'''
out_path = os.path.join(HERE, '..', 'ArithS', 'Necessitation', 'NumIdRows.lean')
open(out_path, 'w').write(header + lib_blocks + mid + new_blocks + mid2 + table_part + footer)
print('wrote', out_path, 'rows:', TABLE)
