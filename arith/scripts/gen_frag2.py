"""gen_frag2.py — generates arith/ArithS/Necessitation/Frag2Rows.lean (2026-09-14):
the node rows for the four remaining tags (`allIntro`, `exsIntro`, `shiftRule`, `axm`) plus the
sequent-plumbing rows the fragments' PROLOGUES cite (`setShiftTotal`, `setShiftInsert`,
`setShiftEmpty`, `setShiftFun`, `shiftMemSetShift`, `qqFvarTotal`, `adjoinTotal`,
`substsSubsts1`, `congShiftL`, `congSetShiftL`) and the `axm` recognizers (`axiomRec σ`,
`indRec`, `totIndBody`), re-issued with quote_row_/inst_ lemmas (via gen_frag.py's gen_row),
and the fragment-2 table `frag2Rows := frag1Rows ++ frag2ExtraRows` (gIdx_<row> = 126 + k),
`Frag2Table` (⇒ `Frag1Table`), `exists_frag2Table`, `frag2Pieces` extending `frag1Pieces`,
per row `frag2Table_<row>`, `gmk_<row>`, `gtag_<row>`, `gok_<row>`, plus `gfok_<row>`: the
Frag1 rows Frag2 uses, read from `frag2Pieces`.
Run from arith/: python3 scripts/gen_frag2.py
"""
import sys, re, os, types
HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, 'gen_frag.py')).read()
_src = _src[:_src.index('\ngen_frag()\ngen_rowinstb()')].replace("if len(sys.argv) > 3:", "if False:")
G = types.ModuleType('genfrag_lib')
G.__file__ = os.path.join(HERE, 'gen_frag.py')
exec(compile(_src, G.__file__, 'exec'), G.__dict__)
A, EX, S, P, C = G.A, G.EX, G.S, G.P, G.C

# ---- the Δ₁ch predicate (nothing exists for it: the generator produces P/isSem/Fdef/isFormula too)
G.PREDS['axch'] = G.graph('(↑(Theory.Δ₁ch TAct).sigma : ArithmeticSemisentence 1)', 1, 'Paxch', 'axchFact', ['p'],
                          '(Theory.Δ₁ch TAct).sigma', lambda a: f'{a[0]} ∈ TAct.Δ₁Class')


# ---- the rows re-issued with quote_row_/inst_ lemmas (same names, same DSL as the originals)
NEW_ROWS = [
 # Nodes: totalities of the four remaining tags
 ('totAllIntro', ['d', 'p', 's'], [], EX(['e'], [A('allIntro', 'e', 's', 'p', 'd')])),
 ('totExsIntro', ['d', 't', 'p', 's'], [], EX(['e'], [A('exsIntro', 'e', 's', 'p', 't', 'd')])),
 ('totShiftRule', ['d', 's'], [], EX(['e'], [A('shiftRule', 'e', 's', 'd')])),
 ('totAxm', ['p', 's'], [], EX(['e'], [A('axm', 'e', 's', 'p')])),
 # Nodes: intro rows
 ('introAll', ['e', 'c', 'ss', 'fp', 'r', 'd', 'p', 's'],
  [A('allIntro', 'e', 's', 'p', 'd'), A('qqAll', 'r', 'p'), A('mem', 'r', 's'),
   A('fstIdx', 'c', 'd'), A('freeG', 'fp', 'p'), A('setShiftG', 'ss', 's'), A('insert', 'c', 'fp', 'ss'),
   A('deriv', 'd')], A('deriv', 'e')),
 ('introExs', ['e', 'c', 'pt', 'r', 'd', 't', 'p', 's', 'x'],
  [A('exsIntro', 'e', 's', 'p', 't', 'd'), A('qqExs', 'r', 'p'), A('mem', 'r', 's'),
   A('tpi', 'Z', 't'), A('fstIdx', 'c', 'd'), A('substs1G', 'pt', 't', 'p'), A('insert', 'c', 'pt', 's'),
   A('deriv', 'd')], A('deriv', 'e')),
 ('introShift', ['e', 'ss', 'c', 'd'],
  [A('fstIdx', 'c', 'd'), A('setShiftG', 'ss', 'c'), A('deriv', 'd'), A('shiftRule', 'e', 'ss', 'd')],
  A('deriv', 'e')),
 # Nodes: dlen rows
 ('dlenAll', ['l', 'n', 'd', 'p', 's', 'e'],
  [A('allIntro', 'e', 's', 'p', 'd'), A('dlen', 'd', 'n'), A('setLen', 'l', 's')], A('dlen', 'e', S(P('l', 'n')))),
 ('dlenExs', ['lt', 'l', 'n', 'd', 't', 'p', 's', 'e'],
  [A('exsIntro', 'e', 's', 'p', 't', 'd'), A('dlen', 'd', 'n'), A('setLen', 'l', 's'), A('tlenG', 'lt', 't')],
  A('dlen', 'e', S(P(P('l', 'lt'), 'n')))),
 ('dlenShift', ['l', 'n', 'd', 's', 'e'],
  [A('shiftRule', 'e', 's', 'd'), A('dlen', 'd', 'n'), A('setLen', 'l', 's')], A('dlen', 'e', S(P('l', 'n')))),
 ('dlenAxm', ['l', 'p', 's', 'e'], [A('axm', 'e', 's', 'p'), A('setLen', 'l', 's')], A('dlen', 'e', S('l'))),
 # Sets / prologue plumbing
 ('introAxm', ['e', 'p', 's'],
  [A('fsetPi', 's'), A('mem', 'p', 's'), A('axch', 'p'), A('axm', 'e', 's', 'p')], A('deriv', 'e')),
 ('setShiftTotal', ['s'], [], EX(['t'], [A('setShiftG', 't', 's')])),
 ('shiftMemSetShift', ['y', 't', 'x', 's'],
  [A('mem', 'x', 's'), A('setShiftG', 't', 's'), A('shiftG', 'y', 'x')], A('mem', 'y', 't')),
]
# `introAxmB` is at arity 3; its `Δ₁ch` antecedent gets its own predicate (registered above).

G.out = []
for (name, binders, ants, conc) in NEW_ROWS:
    G.gen_row(name, binders, ants, conc)
new_blocks = '\n'.join(G.out)

# ---- the table rows: the new rows, then the RowInstB rows Frag2 needs
TABLE = [n for (n, *_r) in NEW_ROWS] + [
 'fstIdxAll', 'fstIdxExs', 'fstIdxShift',
 'setShiftInsert', 'setShiftEmpty', 'setShiftFun', 'congShiftL', 'congSetShiftL', 'substsSubsts1',
]
BASE = 126
rowinstb = open('ArithS/Necessitation/RowInstB.lean').read()
rowinst = open('ArithS/Necessitation/RowInst.lean').read()
alltext = rowinstb + '\n' + rowinst + '\n' + new_blocks

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
E('/-! ## 2. The fragment-2 table: the Frag1 rows, then the new rows at `126 + k` -/')
E('')
E('section frag2Table')
E('')
for k, name in enumerate(TABLE):
    E(f'def gIdx_{name} : ℕ := {BASE + k}')
E(f'def frag2RowCount : ℕ := {BASE + len(TABLE)}')
E('')
E('/-- The rows at `126 + k`, in index order. -/')
E('noncomputable def frag2ExtraRows : List WRow := [')
E(',\n'.join(f'  ⟨{info[n]["m"]}, {n}B, lib_{n}⟩' for n in TABLE))
E(']')
E('')
E("/-- The fragment-2 table's rows: Frag1's, then the extra rows. -/")
E('noncomputable def frag2Rows : List WRow := frag1Rows ++ frag2ExtraRows')
E('')
E('lemma frag2Rows_length : frag2Rows.length = frag2RowCount := rfl')
E('')
E('/-- **The fragment-2 proof table**: `frag2RowCount` rows at least, the `i`-th with the arity and the')
E('matrix of `frag2Rows[i]`. -/')
E('def Frag2Table (tbl : V) : Prop :=')
E('  (frag2RowCount : V) ≤ len tbl ∧')
E('  ∀ (i : ℕ) (h : i < frag2Rows.length),')
E('    rowM tbl.[(i : V)] = ((frag2Rows[i]).m : V) ∧ rowB tbl.[(i : V)] = ⌜Semiformula.lMap emb (frag2Rows[i]).B⌝')
E('')
E('/-- A fragment-2 table is a fragment-1 table (the first 126 rows). -/')
E('lemma Frag2Table.frag1Table {tbl : V} (h : Frag2Table tbl) : Frag1Table tbl := by')
E('  refine ⟨le_trans (by exact_mod_cast (by decide : frag1RowCount ≤ frag2RowCount)) h.1, ?_⟩')
E('  intro i hi')
E("  have hi' : i < frag2Rows.length := by")
E('    rw [frag2Rows_length]; exact lt_of_lt_of_le (frag1Rows_length ▸ hi) (by decide)')
E("  have := h.2 i hi'")
E('  rwa [show frag2Rows[i] = frag1Rows[i] from List.getElem_append_left hi] at this')
E('')
E('lemma Frag2Table.layoutTable {tbl : V} (h : Frag2Table tbl) : LayoutTable tbl := h.frag1Table.layoutTable')
E('lemma Frag2Table.walkTable {tbl : V} (h : Frag2Table tbl) : WalkTable tbl := h.frag1Table.walkTable')
E('')
E('/-- **The fragment-2 proof table exists in every model, with one standard length bound.** -/')
E('theorem exists_frag2Table : ∃ N : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],')
E('    ∃ tbl : V, TableOK tbl (N : V) ∧ Frag2Table tbl := by')
E('  obtain ⟨N, hN⟩ := exists_rows frag2Rows')
E('  refine ⟨N, fun V _ _ ↦ ?_⟩')
E('  obtain ⟨rows, hlen, hok, hidx⟩ := hN V')
E('  refine ⟨vecOf rows, tableOK_vecOf rows hok, ?_, ?_⟩')
E('  · rw [len_vecOf, hlen, frag2Rows_length]')
E('  · intro i h')
E("    have h' : i < rows.length := by rw [hlen]; exact h")
E('    rw [nth_vecOf rows i h\']')
E("    exact hidx i h h'")
E('')
E('lemma frag2Table_len {tbl : V} (h : Frag2Table tbl) (i : ℕ) (hi : i < frag2RowCount) : ((i : ℕ) : V) < len tbl :=')
E('  lt_of_lt_of_le (by exact_mod_cast hi) h.1')
E('')
E('/-! ### The per-row readings of `Frag2Table` -/')
E('')
for name in TABLE:
    d = info[name]
    c = f'(^∃ row_{name}_R)' if d['tag2'] else f'row_{name}_c'
    E(f'lemma frag2Table_{name} {{tbl : V}} (h : Frag2Table tbl) :')
    E(f'    rowM tbl.[((gIdx_{name} : ℕ) : V)] = (({d["m"]} : ℕ) : V) ∧')
    E(f'    rowB tbl.[((gIdx_{name} : ℕ) : V)] = impChainV LAct (vecOf row_{name}_as) {c} := by')
    E(f'  have this : rowM tbl.[((gIdx_{name} : ℕ) : V)] = (({d["m"]} : ℕ) : V) ∧')
    E(f'      rowB tbl.[((gIdx_{name} : ℕ) : V)] = ⌜Semiformula.lMap emb {name}B⌝ :=')
    E(f'    h.2 gIdx_{name} (Nat.lt_of_sub_eq_succ rfl)')
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
        E(f'noncomputable def gpiece_{name} : V := ⟪(2 : V), vecOf row_{name}_as, row_{name}_R⟫')
    else:
        E(f'noncomputable def gpiece_{name} : V := ⟪(0 : V), vecOf row_{name}_as, row_{name}_c⟫')
E('')
E('noncomputable def frag2ExtraPieceList : List V := [')
E(',\n'.join(f'  gpiece_{n}' for n in TABLE))
E(']')
E('')
E("/-- **The piece table of the Frag2 producers**: Frag1's pieces, then the extra rows' pieces. -/")
E('noncomputable def frag2Pieces : V := vecOf (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList)')
E('')
E('lemma frag2Pieces_nth_lt (i : ℕ) (hi : i < frag1RowCount) : (frag2Pieces : V).[(i : V)] = (frag1Pieces : V).[(i : V)] := by')
E('  unfold frag2Pieces frag1Pieces')
E('  have h1 : i < (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList : List V).length := by')
E('    rw [show (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList ++ frag2ExtraPieceList : List V).length = frag2RowCount from rfl]')
E('    exact lt_of_lt_of_le hi (by decide)')
E('  have h2 : i < (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList : List V).length := by')
E('    rw [show (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList : List V).length = frag1RowCount from rfl]; exact hi')
E('  rw [nth_vecOf _ i h1, nth_vecOf _ i h2]')
E('  exact List.getElem_append_left h2')
E('')
E("/-- A Frag1 step read from the Frag2 pieces is Frag1's step. -/")
E('lemma mkStep_frag2Pieces_lt (i : ℕ) (hi : i < frag1RowCount) (ev : V) :')
E('    mkStep frag2Pieces (i : V) ev = mkStep frag1Pieces (i : V) ev := by')
E('  rw [mkStep, mkStep, frag2Pieces_nth_lt i hi]')
E('')
for name in TABLE:
    d = info[name]
    idx = BASE + TABLE.index(name)
    E(f'lemma frag2Pieces_{name} : (frag2Pieces : V).[((gIdx_{name} : ℕ) : V)] = gpiece_{name} := by')
    E(f'  unfold frag2Pieces')
    E(f'  rw [nth_vecOf _ gIdx_{name} (Nat.lt_of_sub_eq_succ rfl)]')
    E(f'  rfl')
    E('')
    if d['tag2']:
        E(f'lemma gmk_{name} (ev : V) :')
        E(f'    mkStep frag2Pieces ((gIdx_{name} : ℕ) : V) ev = sIntroFact ((gIdx_{name} : ℕ) : V) ev (vecOf row_{name}_as) row_{name}_R := by')
        E(f'  rw [mkStep, frag2Pieces_{name}]')
        E(f'  simp [gpiece_{name}, sIntroFact]')
        E('')
        E(f'lemma gtag_{name} {{W : V}} (hWp : W = frag2Pieces) (ev : V) : sTag (mkStep W ({idx} : V) ev) = 2 := by')
        E(f'  subst hWp')
        E(f'  have hk : ((gIdx_{name} : ℕ) : V) = ({idx} : V) := by simp [gIdx_{name}]')
        E(f'  rw [← hk, gmk_{name}]; simp')
    else:
        E(f'lemma gmk_{name} (ev : V) :')
        E(f'    mkStep frag2Pieces ((gIdx_{name} : ℕ) : V) ev = sUseHorn ((gIdx_{name} : ℕ) : V) ev (vecOf row_{name}_as) row_{name}_c := by')
        E(f'  rw [mkStep, frag2Pieces_{name}]')
        E(f'  simp [gpiece_{name}, sUseHorn]')
        E('')
        E(f'lemma gtag_{name} {{W : V}} (hWp : W = frag2Pieces) (ev : V) : sTag (mkStep W ({idx} : V) ev) = 0 := by')
        E(f'  subst hWp')
        E(f'  have hk : ((gIdx_{name} : ℕ) : V) = ({idx} : V) := by simp [gIdx_{name}]')
        E(f'  rw [← hk, gmk_{name}]; simp')
    E('')
E('/-! ### The per-row applicability lemmas `gok_<row>` -/')
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
    if d['tag2']:
        after = f'insert (neg LAct ({conc})) (setShift LAct Γ)'
    else:
        after = f'insert (neg LAct ({conc})) Γ'
    E(f'/-- Row `{name}` as a step. -/')
    E(f'lemma gok_{name} {{tbl N E Γ W : V}} {binders}(htbl : TableOK tbl N) (hF : Frag2Table tbl) (hWp : W = frag2Pieces)')
    E(f'    (hΓ : IsFormulaSet LAct Γ) {hyps} {mems} :')
    E(f'    StepOK tbl E (({Mcap} : ℕ) : V) Γ (mkStep W {idx} {vec}) ∧ sTag (mkStep W {idx} {vec}) = {tag} ∧')
    E(f'    ctxAfter Γ (mkStep W {idx} {vec}) = {after} := by')
    E(f'  subst hWp')
    E(f'  have hk : ((gIdx_{name} : ℕ) : V) = ({idx} : V) := by simp [gIdx_{name}]')
    E(f'  have hstep := gmk_{name} (V := V) {vec}')
    E(f'  have hlen := frag2Table_len hF gIdx_{name} (by decide)')
    E(f'  have hrow := frag2Table_{name} hF')
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

# ---- the Frag1 rows Frag2 uses, transferred to the Frag2 pieces
FRAG1_USED = ['leRefl', 'leTrans', 'dlenLeafLe', 'dlenUnaryLe', 'dlenBinaryLe', 'congFstIdx',
              'introAxm', 'fstIdxAxm', 'dlenAxm2']
# `introAxm`/`fstIdxAxm` live in Frag1Rows? — resolved below by presence test
frag1 = open('ArithS/Necessitation/Frag1Rows.lean').read()
FRAG1_USED = [n for n in FRAG1_USED if ('lemma fok_%s ' % n) in frag1]
E('/-! ### The Frag1 rows Frag2 uses, read from the Frag2 pieces (`gfok_<row>` from `fok_<row>`) -/')
E('')
for name in FRAG1_USED:
    li = frag1.index('lemma fok_%s ' % name)
    stmt = frag1[li: frag1.index(':= by', li)]
    idxm = re.search(r'def fIdx_%s : ℕ := (\d+)' % name, frag1)
    idx = int(idxm.group(1))
    head, rest = stmt.split('(htbl : TableOK tbl N) (hF : Frag1Table tbl) (hWp : W = frag1Pieces)', 1)
    head = head.replace('lemma fok_%s' % name, 'lemma gfok_%s' % name)
    E(head + '(htbl : TableOK tbl N) (hF : Frag2Table tbl) (hWp : W = frag2Pieces)' + rest + ':= by')
    E('  subst hWp')
    E(f'  have e : ∀ ev : V, mkStep frag2Pieces ({idx} : V) ev = mkStep frag1Pieces ({idx} : V) ev := fun ev ↦ by')
    E(f'    have := mkStep_frag2Pieces_lt {idx} (by decide) ev; simpa using this')
    E('  rw [e]')
    args = re.findall(r"\((h[A-Za-zΓ0-9₀₁₂₃₄₅₆₇₈₉']*) :", rest)
    E(f'  exact fok_{name} htbl hF.frag1Table rfl {" ".join(args)}')
    E('')
# the layout rows Frag2 uses, transferred
LAYOUT_USED = ['eqRefl', 'eqSymm', 'insertTotalC', 'memInsertSelfC', 'subsetInsertC', 'subsetTransC',
               'subsetMemC', 'emptySubsetC', 'isFormulaSetInsertC', 'fsetSigmaPiC', 'setLenTotalC',
               'subsetReflC', 'subsetAntisymm', 'congMem']
E('/-! ### The layout rows Frag2 uses, read from the Frag2 pieces -/')
E('')
for name in LAYOUT_USED:
    li = frag1.index('lemma flok_%s ' % name)
    stmt = frag1[li: frag1.index(':= by', li)]
    layout = open('ArithS/Necessitation/Layout.lean').read()
    idxm = re.search(r'def lIdx_%s : ℕ := (\d+)' % name, layout)
    idx = int(idxm.group(1))
    head, rest = stmt.split('(htbl : TableOK tbl N) (hF : Frag1Table tbl) (hWp : W = frag1Pieces)', 1)
    head = head.replace('lemma flok_%s' % name, 'lemma glok_%s' % name)
    E(head + '(htbl : TableOK tbl N) (hF : Frag2Table tbl) (hWp : W = frag2Pieces)' + rest + ':= by')
    E('  subst hWp')
    E(f'  have e : ∀ ev : V, mkStep frag2Pieces ({idx} : V) ev = mkStep frag1Pieces ({idx} : V) ev := fun ev ↦ by')
    E(f'    have := mkStep_frag2Pieces_lt {idx} (by decide) ev; simpa using this')
    E('  rw [e]')
    args = re.findall(r"\((h[A-Za-zΓ0-9₀₁₂₃₄₅₆₇₈₉']*) :", rest)
    E(f'  exact flok_{name} htbl hF.frag1Table rfl {" ".join(args)}')
    E('')
E('end frag2Table')

head = '''import ArithS.Necessitation.Frag1Rows

/-!
# ArithS.Necessitation.Frag2Rows — the fragment-2 table (GENERATED by `arith/scripts/gen_frag2.py`)

1. The rows the four remaining fragments (`allIntro`, `exsIntro`, `shiftRule`, `axm`) use, re-issued
   with their `quote_row_`/`inst_` lemmas (the originals in `Lib/Nodes.lean`, `Lib/Sets.lean`,
   `Lib/Frag.lean`; blocks produced by `gen_frag.py`'s `gen_row`, same names, same DSL): the
   totalities `totAllIntro`/`totExsIntro`/`totShiftRule`/`totAxm`, the `introAll`/`introExs`/
   `introShift` and `dlenAll`/`dlenExs`/`dlenShift`/`dlenAxm` node rows, and the sequent plumbing
   `setShiftTotal`, `shiftMemSetShift`.
2. The fragment-2 table: `frag2Rows := frag1Rows ++ frag2ExtraRows` — Frag1's 126 rows at their
   indices, then the rows above and the `fstIdx<Tag>`/`setShift*`/congruence rows of `RowInstB` at
   `gIdx_<row> = 126 + k`. `Frag2Table tbl` (implies `Frag1Table tbl`), `exists_frag2Table`, the
   piece table `frag2Pieces` extending `frag1Pieces` entrywise (`mkStep_frag2Pieces_lt`), and per
   row `frag2Table_<row>`, `gmk_<row>`, `gtag_<row>`, `gok_<row>`, plus `gfok_<row>`/`glok_<row>`:
   the Frag1 and layout rows Frag2 uses, read from `frag2Pieces`.

NOTE: `introAxm`'s `(Theory.Δ₁ch TAct).sigma p` antecedent gets the NEW predicate code `Paxch` /
fact code `axchFact` here (nothing in `RowInstB` had it); `nodeAxm` (Frag2.lean) therefore takes
`axchFact p` in the context as a LAYOUT HYPOTHESIS — the recognizer chain that produces it (`axiomRec σ`
for the finitely many standard axioms, `indRec` for the induction schema) is NOT in this table.
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

/-! ## 0. The `Δ₁ch` predicate code (nothing in `RowInstB.lean` had it) -/

section axch

/-- The code of `(Theory.Δ₁ch TAct).sigma`, the `axm` premise `p ∈ TAct.Δ₁Class`. -/
noncomputable def Paxch : V := ⌜Semiformula.lMap emb (↑(Theory.Δ₁ch TAct).sigma : ArithmeticSemisentence 1)⌝
lemma isSemiformula_Paxch : IsSemiformula LAct ((1 : ℕ) : V) Paxch := Sentence.quote_isSemiformula _
lemma shift_Paxch : shift LAct (Paxch : V) = Paxch := shift_quote_sentence _
lemma fvOccF_Paxch : fvOccF LAct (Paxch : V) = 0 := fvOccF_quote_sentence _

/-- `p ∈ TAct.Δ₁Class` at the witness `p`. -/
noncomputable def axchFact (p : V) : V := subst LAct (listToVec [p]) Paxch
lemma isFormula_axchFact {p : V} (hp : IsSemiterm LAct 0 p) : IsFormula LAct (axchFact p) :=
  isFormula_fact isSemiformula_Paxch _ rfl (List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩)
lemma shift_axchFact {p : V} (hp : IsSemiterm LAct 0 p) :
    shift LAct (axchFact p) = axchFact (termShift LAct p) := by
  unfold axchFact
  rw [shift_subst_listToVec [p] isSemiformula_Paxch shift_Paxch (n := 0) (List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩)]
  rfl
lemma formulaLen_axchFact_le {B : V} (hB : 1 ≤ B) {p : V} (hp : IsSemiterm LAct 0 p) (hlp : termLen LAct p ≤ B) :
    formulaLen LAct (axchFact p) ≤ formulaLen LAct (Paxch : V) * B :=
  formulaLen_fact_le hB isSemiformula_Paxch _ rfl (List.forall_mem_cons.mpr ⟨⟨hp, hlp⟩, List.forall_mem_nil _⟩)
lemma fvOccF_axchFact_le {M : V} {p : V} (hp : IsSemiterm LAct 0 p) (hop : fvOcc LAct p ≤ M) :
    fvOccF LAct (axchFact p) ≤ bvOccF LAct (Paxch : V) * M :=
  fvOccF_fact_le isSemiformula_Paxch fvOccF_Paxch _ rfl (List.forall_mem_cons.mpr ⟨⟨hp, hop⟩, List.forall_mem_nil _⟩)

end axch

/-! ## 1. The rows, re-issued -/

section frag2Rows

'''
open('ArithS/Necessitation/Frag2Rows.lean','w').write(head + new_blocks + '\nend frag2Rows\n\n' + '\n'.join(o) + '\n\nend ArithS\n')
print('rows', len(TABLE), 'frag1 used', len(FRAG1_USED))
