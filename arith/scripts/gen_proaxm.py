"""gen_proaxm.py — generates arith/ArithS/Necessitation/ProAxmRows.lean (2026-09-15):
the ONE row the `axm` prologue (`ProAxm.lean`, `DESIGN_fragments.md` §4.10 (i)) needs beyond the pin table, on
the `gen_numid.py` template: `congAxch` — `!axch x → y = x → !axch y`, the congruence of the `TAct`-axiom
recognizer `(Theory.Δ₁ch TAct).sigma` (predicate code `Paxch`/fact code `axchFact`, `Frag2Rows.lean`) along an
equality. With it, case (i) of `axm` is NumId's numeral identification `eqFact &ip (numeral ⌜σ⌝)` + ONE closed
`Lib` fact `axchFact (numeral ⌜σ⌝)` (an `sLemma`) + ONE Horn step — no per-σ row (`axiomRec σ` is parametric in
σ; `congAxch` is not). Placed at `aIdx_<row> = numIdRowCount + k` (APPEND-ONLY after the pin table, SYMBOLIC in
`numIdRowCount`), the piece table `proAxmPieces` extending `numIdPieces` entrywise, per row `amk_`/`atag_`/`aok_`
against EXPLICIT table readings (`hlen`, `hrow`) — `ProAxmTable` lives in `ProAxm.lean`.
Run from arith/: python3 scripts/gen_proaxm.py
"""
import sys, re, os, types
HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, 'gen_frag.py')).read()
_src = _src[:_src.index('\ngen_frag()\ngen_rowinstb()')].replace("if len(sys.argv) > 3:", "if False:")
G = types.ModuleType('genfrag_lib')
G.__file__ = os.path.join(HERE, 'gen_frag.py')
exec(compile(_src, G.__file__, 'exec'), G.__dict__)
A, EX, S, P, C, M, by = G.A, G.EX, G.S, G.P, G.C, G.M, G.by

# the Δ₁ch predicate: its codes `Paxch`/`axchFact` are hand-written in `Frag2Rows.lean` §0 (registered as in gen_frag2.py)
G.PREDS['axch'] = G.graph('(↑(Theory.Δ₁ch TAct).sigma : ArithmeticSemisentence 1)', 1, 'Paxch', 'axchFact', ['p'],
                          '(Theory.Δ₁ch TAct).sigma', lambda a: f'{a[0]} ∈ TAct.Δ₁Class')

EXISTING = []
NEW_ROWS = [
 ('congAxch', ['y', 'x'], [A('axch', 'x'), A('eq', 'y', 'x')], A('axch', 'y'), None,
  "`x ∈ TAct.Δ₁Class → y = x → y ∈ TAct.Δ₁Class` — the recognizer `(Theory.Δ₁ch TAct).sigma` along an equality (the `axm`(i) closing step: `axchFact (numeral ⌜σ⌝)` and `&ip = numeral ⌜σ⌝` give `axchFact &ip`)."),
]
TABLE = EXISTING + [n for (n, *_r) in NEW_ROWS]

G.frag = []; G.out = []
for (name, binders, ants, conc, proof, doc) in NEW_ROWS:
    G.gen_frag_row('proaxm', name, binders, ants, conc, proof, doc)
    G.gen_row(name, binders, ants, conc)
lib_blocks = '\n'.join(G.frag)
new_blocks = '\n'.join(G.out)
alltext = new_blocks

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

PIECES_PREFIX = 'walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList ++ topExtraPieceList ++ proExtraPieceList ++ numIdPadPieceList ++ numIdExtraPieceList'

o = []
E = o.append
E('/-! ## 2. The extra rows at `numIdRowCount + k`, the piece table, the applicability lemmas -/')
E('')
E('section proAxmRowsTable')
E('')
for k, name in enumerate(TABLE):
    E(f'def aIdx_{name} : ℕ := numIdRowCount + {k}')
E(f'def proAxmExtraRowCount : ℕ := {len(TABLE)}')
E('')
E('/-- The extra rows at `numIdRowCount + k`, in index order (append-only). -/')
E('noncomputable def proAxmExtraRows : List WRow := [')
E(',\n'.join(f'  ⟨{info[n]["m"]}, {n}B, lib_{n}⟩' for n in TABLE))
E(']')
E('')
E('lemma proAxmExtraRows_length : proAxmExtraRows.length = proAxmExtraRowCount := rfl')
E('')
E("/-- **The `axm` table's rows**: the pin's rows, then the `axm` rows. -/")
E('noncomputable def proAxmRows : List WRow := numIdRows ++ proAxmExtraRows')
E('def proAxmRowCount : ℕ := numIdRowCount + proAxmExtraRowCount')
E('lemma proAxmRows_length : proAxmRows.length = proAxmRowCount := by')
E('  simp only [proAxmRows, List.length_append, numIdRows_length, proAxmExtraRows_length, proAxmRowCount]')
E('')
E('/-! ### The piece table -/')
E('')
for name in TABLE:
    E(f'noncomputable def apiece_{name} : V := ⟪(0 : V), vecOf row_{name}_as, row_{name}_c⟫')
E('')
E('noncomputable def proAxmExtraPieceList : List V := [')
E(',\n'.join(f'  apiece_{n}' for n in TABLE))
E(']')
E('')
E("/-- **The piece table of the `axm` prologue**: the pin's pieces, then the extra rows' pieces. -/")
E(f'noncomputable def proAxmPieces : V := vecOf ({PIECES_PREFIX} ++ proAxmExtraPieceList)')
E('')
E('set_option maxHeartbeats 1000000 in')
E('lemma proAxmPieces_nth_lt (i : ℕ) (hi : i < numIdRowCount) : (proAxmPieces : V).[(i : V)] = (numIdPieces : V).[(i : V)] := by')
E('  unfold proAxmPieces numIdPieces')
E(f'  have h1 : i < ({PIECES_PREFIX} ++ proAxmExtraPieceList : List V).length := by')
E(f'    rw [show ({PIECES_PREFIX} ++ proAxmExtraPieceList : List V).length = proAxmRowCount from rfl]')
E('    exact lt_of_lt_of_le hi (by simp only [proAxmRowCount]; omega)')
E(f'  have h2 : i < ({PIECES_PREFIX} : List V).length := by')
E(f'    rw [show ({PIECES_PREFIX} : List V).length = numIdRowCount from rfl]; exact hi')
E('  rw [nth_vecOf _ i h1, nth_vecOf _ i h2]')
E('  exact List.getElem_append_left h2')
E('')
E("/-- A pin step read from the `axm` pieces is the pin's step. -/")
E('lemma mkStep_proAxmPieces_lt (i : ℕ) (hi : i < numIdRowCount) (ev : V) :')
E('    mkStep proAxmPieces (i : V) ev = mkStep numIdPieces (i : V) ev := by')
E('  rw [mkStep, mkStep, proAxmPieces_nth_lt i hi]')
E('')
for name in TABLE:
    E('set_option maxHeartbeats 1000000 in')
    E(f'lemma proAxmPieces_{name} : (proAxmPieces : V).[((aIdx_{name} : ℕ) : V)] = apiece_{name} := by')
    E(f'  unfold proAxmPieces')
    E(f'  rw [nth_vecOf _ aIdx_{name} (Nat.lt_of_sub_eq_succ rfl)]')
    E(f'  rfl')
    E('')
    E(f'lemma amk_{name} (ev : V) :')
    E(f'    mkStep proAxmPieces ((aIdx_{name} : ℕ) : V) ev = sUseHorn ((aIdx_{name} : ℕ) : V) ev (vecOf row_{name}_as) row_{name}_c := by')
    E(f'  rw [mkStep, proAxmPieces_{name}]')
    E(f'  simp [apiece_{name}, sUseHorn]')
    E('')
    E(f'lemma atag_{name} {{W : V}} (hWp : W = proAxmPieces) (ev : V) : sTag (mkStep W ((aIdx_{name} : ℕ) : V) ev) = 0 := by')
    E(f'  subst hWp')
    E(f'  rw [amk_{name}]; simp')
    E('')
E('/-! ### The per-row applicability lemmas `aok_<row>` (against explicit table readings) -/')
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
    idx = f'((aIdx_{name} : ℕ) : V)'
    E(f'/-- Row `{name}` as a step, against the table readings `hlen`/`hrow` at its index. -/')
    E(f'lemma aok_{name} {{tbl N E Γ W : V}} {binders}(htbl : TableOK tbl N) (hWp : W = proAxmPieces)')
    E(f'    (hlen : {idx} < len tbl)')
    E(f'    (hrow : rowM tbl.[{idx}] = (({d["m"]} : ℕ) : V) ∧')
    E(f'      rowB tbl.[{idx}] = impChainV LAct (vecOf row_{name}_as) row_{name}_c)')
    E(f'    (hΓ : IsFormulaSet LAct Γ) {hyps} {mems} :')
    E(f'    StepOK tbl E (({Mcap} : ℕ) : V) Γ (mkStep W {idx} {vec}) ∧ sTag (mkStep W {idx} {vec}) = 0 ∧')
    E(f'    ctxAfter Γ (mkStep W {idx} {vec}) = insert (neg LAct ({conc})) Γ := by')
    E(f'  subst hWp')
    E(f'  have hstep := amk_{name} (V := V) {vec}')
    E(f'  have hes : ∀ e ∈ {lst}, IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := {hes_term}')
    E(f'  have hinst := inst_{name} {inst_args}')
    E(f'  rw [hstep, show ({vec} : V) = vecOf {lst} from rfl]')
    E(f'  refine ⟨stepOK_useHorn htbl {lst} row_{name}_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : {len(ws)} ≤ {Mcap}))')
    E(f'    (by rw [show row_{name}_as.length = {len(facts)} from rfl] <;> exact_mod_cast (by decide : {len(facts)} ≤ {Mcap})) hes ?_, by simp, ?_⟩')
    E(f'  · exact neg_mem_of_map hinst.1 ({mem_term})')
    E(f'  · rw [ctxAfter_useHorn {lst} row_{name}_as isSemiformula_{name}_c (fun e he ↦ (hes e he).1), hinst.2]')
    E('')
E('end proAxmRowsTable')
table_part = '\n'.join(o)

header = '''import ArithS.Necessitation.NumIdRows
import ArithS.Necessitation.Frag2Rows

/-!
# ArithS.Necessitation.ProAxmRows — the `axm` prologue's row (GENERATED by `arith/scripts/gen_proaxm.py`)

ONE new row beyond the pin table (`NumIdRows.lean`): `congAxch` — `!axch x → y = x → !axch y`, the congruence
of the `TAct`-axiom recognizer `(Theory.Δ₁ch TAct).sigma` (predicate code `Paxch`, fact code `axchFact`,
`Frag2Rows.lean` §0) along an equality. It is the closing step of `axm` case (i) (`DESIGN_fragments.md` §4.10 (i),
`ProAxm.lean`): from NumId's `eqFact &ip (numeral ⌜σ⌝)` and the closed `Lib` fact `axchFact (numeral ⌜σ⌝)` (an
`sLemma`) it concludes `axchFact &ip` — ONE row for every standard axiom σ, where `Lib/Nodes.lean`'s `axiomRec σ`
would need one row per σ. The extra rows `proAxmExtraRows` sit at `aIdx_<row> = numIdRowCount + k` — APPEND-ONLY
after the pin table and SYMBOLIC in `numIdRowCount`; the piece table `proAxmPieces` extends `numIdPieces`
entrywise; per row `amk_<row>`, `atag_<row>`, `aok_<row>` — the applicability lemmas take the table readings at
the row's index as EXPLICIT hypotheses; `ProAxmTable` lives in `ProAxm.lean`.
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

section proAxmLib

'''
mid = '''
end proAxmLib

/-! ## 1. Its `quote_row_`/`inst_` block (the `RowInstB` template) -/

section proAxmRowInst

'''
mid2 = '''
end proAxmRowInst

'''
footer = '''

end ArithS
'''
out_path = os.path.join(HERE, '..', 'ArithS', 'Necessitation', 'ProAxmRows.lean')
open(out_path, 'w').write(header + lib_blocks + mid + new_blocks + mid2 + table_part + footer)
print('wrote', out_path, 'rows:', TABLE)
