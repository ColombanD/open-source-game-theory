"""gen_frag1.py — generates arith/ArithS/Necessitation/Frag1Rows.lean (2026-09-14):
the node rows of Lib/Nodes.lean (tot/intro/dlen for axL, verumIntro, andIntro, orIntro, wkRule, cutRule),
the dlen bound rows of Lib/Occ.lean, `leTrans`/`setLenInsertLe` of Lib/Lengths.lean, the set rows
`insertSubset`/`memInsertOfMem`/`insertEqOfMem` of Lib/Sets.lean and `negTotal` of Lib/Formulas.lean,
re-issued with quote_row_/inst_ lemmas (via gen_frag.py's gen_row), and the fragment table
(fIdx_<row> = 87 + k after the layout rows, Frag1Table ⇒ LayoutTable, exists_frag1Table, frag1Pieces
extending layoutPieces, per-row readings and fok_<row> applicability lemmas — at M = 8, or M = 9 for the
two nine-witness rows introAnd/dlenAnd — plus flok_<row> transfers of the layout rows Frag1 uses).
Run from arith/: python3 scripts/gen_frag1.py
"""
import sys, re, os, types
HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, 'gen_frag.py')).read()
_src = _src[:_src.index('\ngen_frag()\ngen_rowinstb()')].replace("if len(sys.argv) > 3:", "if False:")
G = types.ModuleType('genfrag_lib')
G.__file__ = os.path.join(HERE, 'gen_frag.py')
exec(compile(_src, G.__file__, 'exec'), G.__dict__)
A, EX, S, P = G.A, G.EX, G.S, G.P

# ---- the rows re-issued with quote_row_/inst_ lemmas (same names, same DSL as the originals)
NEW_ROWS = [
 # Nodes: totalities
 ('totAxL', ['p', 's'], [], EX(['e'], [A('axL', 'e', 's', 'p')])),
 ('totVerumIntro', ['s'], [], EX(['e'], [A('verumIntro', 'e', 's')])),
 ('totAndIntro', ['dq', 'dp', 'q', 'p', 's'], [], EX(['e'], [A('andIntro', 'e', 's', 'p', 'q', 'dp', 'dq')])),
 ('totOrIntro', ['d', 'q', 'p', 's'], [], EX(['e'], [A('orIntro', 'e', 's', 'p', 'q', 'd')])),
 ('totWkRule', ['d', 's'], [], EX(['e'], [A('wkRule', 'e', 's', 'd')])),
 ('totCutRule', ['d₂', 'd₁', 'p', 's'], [], EX(['e'], [A('cutRule', 'e', 's', 'p', 'd₁', 'd₂')])),
 # Nodes: intro rows
 ('introAxL', ['e', 'np', 'p', 's'],
  [A('fsetPi', 's'), A('mem', 'p', 's'), A('negG', 'np', 'p'), A('mem', 'np', 's'), A('axL', 'e', 's', 'p')], A('deriv', 'e')),
 ('introVerum', ['e', 'v', 's'],
  [A('fsetPi', 's'), A('qqVerum', 'v'), A('mem', 'v', 's'), A('verumIntro', 'e', 's')], A('deriv', 'e')),
 ('introAnd', ['e', 'cq', 'cp', 'r', 'dq', 'dp', 'q', 'p', 's'],
  [A('andIntro', 'e', 's', 'p', 'q', 'dp', 'dq'), A('qqAnd', 'r', 'p', 'q'), A('mem', 'r', 's'),
   A('fstIdx', 'cp', 'dp'), A('insert', 'cp', 'p', 's'), A('deriv', 'dp'),
   A('fstIdx', 'cq', 'dq'), A('insert', 'cq', 'q', 's'), A('deriv', 'dq')], A('deriv', 'e')),
 ('introOr', ['e', 'c', "c'", 'r', 'd', 'q', 'p', 's'],
  [A('orIntro', 'e', 's', 'p', 'q', 'd'), A('qqOr', 'r', 'p', 'q'), A('mem', 'r', 's'),
   A('fstIdx', 'c', 'd'), A('insert', "c'", 'q', 's'), A('insert', 'c', 'p', "c'"), A('deriv', 'd')], A('deriv', 'e')),
 ('introWk', ['e', 'c', 'd', 's'],
  [A('fsetPi', 's'), A('fstIdx', 'c', 'd'), A('subset', 'c', 's'), A('deriv', 'd'), A('wkRule', 'e', 's', 'd')], A('deriv', 'e')),
 # `introCutB` is declared at arity 9 with eight names: `#8` (the LAST position) is an unnamed dummy `x`
 ('introCut', ['e', 'c₂', 'np', 'c₁', 'd₂', 'd₁', 'p', 's', 'x'],
  [A('cutRule', 'e', 's', 'p', 'd₁', 'd₂'), A('fstIdx', 'c₁', 'd₁'), A('insert', 'c₁', 'p', 's'), A('deriv', 'd₁'),
   A('fstIdx', 'c₂', 'd₂'), A('negG', 'np', 'p'), A('insert', 'c₂', 'np', 's'), A('deriv', 'd₂')], A('deriv', 'e')),
 # Nodes: dlen rows
 ('dlenAxL', ['l', 'p', 's', 'e'], [A('axL', 'e', 's', 'p'), A('setLen', 'l', 's')], A('dlen', 'e', S('l'))),
 ('dlenVerum', ['l', 's', 'e'], [A('verumIntro', 'e', 's'), A('setLen', 'l', 's')], A('dlen', 'e', S('l'))),
 ('dlenAnd', ['l', 'nq', 'np', 'dq', 'dp', 'q', 'p', 's', 'e'],
  [A('andIntro', 'e', 's', 'p', 'q', 'dp', 'dq'), A('dlen', 'dp', 'np'), A('dlen', 'dq', 'nq'), A('setLen', 'l', 's')],
  A('dlen', 'e', S(P(P('l', 'np'), 'nq')))),
 ('dlenOr', ['l', 'n', 'd', 'q', 'p', 's', 'e'],
  [A('orIntro', 'e', 's', 'p', 'q', 'd'), A('dlen', 'd', 'n'), A('setLen', 'l', 's')], A('dlen', 'e', S(P('l', 'n')))),
 ('dlenWk', ['l', 'n', 'd', 's', 'e'],
  [A('wkRule', 'e', 's', 'd'), A('dlen', 'd', 'n'), A('setLen', 'l', 's')], A('dlen', 'e', S(P('l', 'n')))),
 ('dlenCut', ['l', 'n₂', 'n₁', 'd₂', 'd₁', 'p', 's', 'e'],
  [A('cutRule', 'e', 's', 'p', 'd₁', 'd₂'), A('dlen', 'd₁', 'n₁'), A('dlen', 'd₂', 'n₂'), A('setLen', 'l', 's')],
  A('dlen', 'e', S(P(P('l', 'n₁'), 'n₂')))),
 # Occ: the dlen bounds and the `≤` glue
 ('dlenLeafLe', ['a', 'l', 'n'], [A('eq', 'n', S('l')), A('le', 'l', 'a')], A('le', 'n', S('a'))),
 ('dlenUnaryLe', ['b', 'a', 'np', 'l', 'n'],
  [A('eq', 'n', S(P('l', 'np'))), A('le', 'l', 'a'), A('le', 'np', 'b')], A('le', 'n', S(P('a', 'b')))),
 ('dlenBinaryLe', ['c', 'b', 'a', 'nq', 'np', 'l', 'n'],
  [A('eq', 'n', S(P(P('l', 'np'), 'nq'))), A('le', 'l', 'a'), A('le', 'np', 'b'), A('le', 'nq', 'c')],
  A('le', 'n', S(P(P('a', 'b'), 'c')))),
 ('leAddLeAdd', ['b', 'a', 'z', 'y', 'x'], [A('le', 'x', P('y', 'z')), A('le', 'y', 'a'), A('le', 'z', 'b')], A('le', 'x', P('a', 'b'))),
 ('leRefl', ['x'], [], A('le', 'x', 'x')),
 # Lengths
 ('leTrans', ['x', 'y', 'z'], [A('le', 'x', 'y'), A('le', 'y', 'z')], A('le', 'x', 'z')),
 ('setLenInsertLe', ['lx', 'ls', 'l', 't', 's', 'x'],
  [A('insert', 't', 'x', 's'), A('setLen', 'l', 't'), A('setLen', 'ls', 's'), A('flenG', 'lx', 'x')], A('le', 'l', P('ls', 'lx'))),
 # Sets
 ('insertSubset', ['u', 'x', 't', 's'], [A('subset', 's', 't'), A('mem', 'x', 't'), A('insert', 'u', 'x', 's')], A('subset', 'u', 't')),
 ('memInsertOfMem', ['t', 'y', 's', 'x'], [A('mem', 'x', 's'), A('insert', 't', 'y', 's')], A('mem', 'x', 't')),
 ('insertEqOfMem', ['t', 's', 'x'], [A('mem', 'x', 's'), A('insert', 't', 'x', 's')], A('eq', 't', 's')),
]
# the term-level rows of Lengths.lean are stated with `leF` (= the DSL `≤` by `rfl`): rewrite to the DSL first
PRE_RW = {'leTrans': ('“x y z. x ≤ y → y ≤ z → x ≤ z”', 3)}

G.out = []
for (name, binders, ants, conc) in NEW_ROWS:
    G.gen_row(name, binders, ants, conc)
new_blocks = '\n'.join(G.out)
for name, (dsltext, ar) in PRE_RW.items():
    new_blocks = new_blocks.replace(f'  unfold {name}B ',
        f'  rw [show {name}B = ({dsltext} : ArithmeticSemisentence {ar}) from rfl]\n  unfold ')

# ---- the table rows: the new rows, then the RowInstB rows Frag1 needs (fstIdx per tag, the congruences)
TABLE = [n for (n, *_r) in NEW_ROWS] + [
 'negTotal',
 'fstIdxAxL', 'fstIdxVerum', 'fstIdxAnd', 'fstIdxOr', 'fstIdxWk', 'fstIdxCut',
 'congFstIdx', 'congMemSet', 'congSetLenR', 'congInsertS',
]
BASE = 87
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
E('/-! ## 2. The fragment table: the layout rows, then the node/bound/set rows at `87 + k` -/')
E('')
E('section frag1Table')
E('')
for k, name in enumerate(TABLE):
    E(f'def fIdx_{name} : ℕ := {BASE + k}')
E(f'def frag1RowCount : ℕ := {BASE + len(TABLE)}')
E('')
E('/-- The rows at `87 + k`, in index order. -/')
E('noncomputable def frag1ExtraRows : List WRow := [')
E(',\n'.join(f'  ⟨{info[n]["m"]}, {n}B, lib_{n}⟩' for n in TABLE))
E(']')
E('')
E('/-- The fragment table\'s rows: the layout\'s (walk + copy/identification/chain), then the extra rows. -/')
E('noncomputable def frag1Rows : List WRow := layoutRows ++ frag1ExtraRows')
E('')
E('lemma frag1Rows_length : frag1Rows.length = frag1RowCount := rfl')
E('')
E('/-- **The fragment proof table**: `frag1RowCount` rows at least, the `i`-th with the arity and the matrix')
E('of `frag1Rows[i]`. -/')
E('def Frag1Table (tbl : V) : Prop :=')
E('  (frag1RowCount : V) ≤ len tbl ∧')
E('  ∀ (i : ℕ) (h : i < frag1Rows.length),')
E('    rowM tbl.[(i : V)] = ((frag1Rows[i]).m : V) ∧ rowB tbl.[(i : V)] = ⌜Semiformula.lMap emb (frag1Rows[i]).B⌝')
E('')
E('/-- A fragment table is a layout table (the first 87 rows). -/')
E('lemma Frag1Table.layoutTable {tbl : V} (h : Frag1Table tbl) : LayoutTable tbl := by')
E('  refine ⟨le_trans (by exact_mod_cast (by decide : layoutRowCount ≤ frag1RowCount)) h.1, ?_⟩')
E('  intro i hi')
E('  have hi\' : i < frag1Rows.length := by')
E('    rw [frag1Rows_length]; exact lt_of_lt_of_le (layoutRows_length ▸ hi) (by decide)')
E('  have := h.2 i hi\'')
E('  rwa [show frag1Rows[i] = layoutRows[i] from List.getElem_append_left hi] at this')
E('')
E('lemma Frag1Table.walkTable {tbl : V} (h : Frag1Table tbl) : WalkTable tbl := h.layoutTable.walkTable')
E('')
E('/-- **The fragment proof table exists in every model, with one standard length bound.** -/')
E('theorem exists_frag1Table : ∃ N : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],')
E('    ∃ tbl : V, TableOK tbl (N : V) ∧ Frag1Table tbl := by')
E('  obtain ⟨N, hN⟩ := exists_rows frag1Rows')
E('  refine ⟨N, fun V _ _ ↦ ?_⟩')
E('  obtain ⟨rows, hlen, hok, hidx⟩ := hN V')
E('  refine ⟨vecOf rows, tableOK_vecOf rows hok, ?_, ?_⟩')
E('  · rw [len_vecOf, hlen, frag1Rows_length]')
E('  · intro i h')
E('    have h\' : i < rows.length := by rw [hlen]; exact h')
E('    rw [nth_vecOf rows i h\']')
E('    exact hidx i h h\'')
E('')
E('lemma frag1Table_len {tbl : V} (h : Frag1Table tbl) (i : ℕ) (hi : i < frag1RowCount) : ((i : ℕ) : V) < len tbl :=')
E('  lt_of_lt_of_le (by exact_mod_cast hi) h.1')
E('')
E('/-! ### The per-row readings of `Frag1Table` -/')
E('')
for name in TABLE:
    d = info[name]
    c = f'(^∃ row_{name}_R)' if d['tag2'] else f'row_{name}_c'
    E(f'lemma frag1Table_{name} {{tbl : V}} (h : Frag1Table tbl) :')
    E(f'    rowM tbl.[((fIdx_{name} : ℕ) : V)] = (({d["m"]} : ℕ) : V) ∧')
    E(f'    rowB tbl.[((fIdx_{name} : ℕ) : V)] = impChainV LAct (vecOf row_{name}_as) {c} := by')
    E(f'  have this : rowM tbl.[((fIdx_{name} : ℕ) : V)] = (({d["m"]} : ℕ) : V) ∧')
    E(f'      rowB tbl.[((fIdx_{name} : ℕ) : V)] = ⌜Semiformula.lMap emb {name}B⌝ :=')
    E(f'    h.2 fIdx_{name} (Nat.lt_of_sub_eq_succ rfl)')
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
        E(f'noncomputable def fpiece_{name} : V := ⟪(2 : V), vecOf row_{name}_as, row_{name}_R⟫')
    else:
        E(f'noncomputable def fpiece_{name} : V := ⟪(0 : V), vecOf row_{name}_as, row_{name}_c⟫')
E('')
E('noncomputable def frag1ExtraPieceList : List V := [')
E(',\n'.join(f'  fpiece_{n}' for n in TABLE))
E(']')
E('')
E('/-- **The piece table of the fragment producers**: the layout\'s pieces, then the extra rows\' pieces. -/')
E('noncomputable def frag1Pieces : V := vecOf (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList)')
E('')
E('lemma frag1Pieces_nth_lt (i : ℕ) (hi : i < layoutRowCount) : (frag1Pieces : V).[(i : V)] = (layoutPieces : V).[(i : V)] := by')
E('  unfold frag1Pieces layoutPieces')
E('  have h1 : i < (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList : List V).length := by')
E('    rw [show (walkPieceList ++ layoutExtraPieceList ++ frag1ExtraPieceList : List V).length = frag1RowCount from rfl]')
E('    exact lt_of_lt_of_le hi (by decide)')
E('  have h2 : i < (walkPieceList ++ layoutExtraPieceList : List V).length := by')
E('    rw [show (walkPieceList ++ layoutExtraPieceList : List V).length = layoutRowCount from rfl]; exact hi')
E('  rw [nth_vecOf _ i h1, nth_vecOf _ i h2]')
E('  exact List.getElem_append_left h2')
E('')
E('/-- A layout step read from the fragment pieces is the layout\'s step. -/')
E('lemma mkStep_frag1Pieces_lt (i : ℕ) (hi : i < layoutRowCount) (ev : V) :')
E('    mkStep frag1Pieces (i : V) ev = mkStep layoutPieces (i : V) ev := by')
E('  rw [mkStep, mkStep, frag1Pieces_nth_lt i hi]')
E('')
for name in TABLE:
    d = info[name]
    idx = BASE + TABLE.index(name)
    E(f'lemma frag1Pieces_{name} : (frag1Pieces : V).[((fIdx_{name} : ℕ) : V)] = fpiece_{name} := by')
    E(f'  unfold frag1Pieces')
    E(f'  rw [nth_vecOf _ fIdx_{name} (Nat.lt_of_sub_eq_succ rfl)]')
    E(f'  rfl')
    E('')
    if d['tag2']:
        E(f'lemma fmk_{name} (ev : V) :')
        E(f'    mkStep frag1Pieces ((fIdx_{name} : ℕ) : V) ev = sIntroFact ((fIdx_{name} : ℕ) : V) ev (vecOf row_{name}_as) row_{name}_R := by')
        E(f'  rw [mkStep, frag1Pieces_{name}]')
        E(f'  simp [fpiece_{name}, sIntroFact]')
        E('')
        E(f'lemma ftag_{name} {{W : V}} (hWp : W = frag1Pieces) (ev : V) : sTag (mkStep W ({idx} : V) ev) = 2 := by')
        E(f'  subst hWp')
        E(f'  have hk : ((fIdx_{name} : ℕ) : V) = ({idx} : V) := by simp [fIdx_{name}]')
        E(f'  rw [← hk, fmk_{name}]; simp')
    else:
        E(f'lemma fmk_{name} (ev : V) :')
        E(f'    mkStep frag1Pieces ((fIdx_{name} : ℕ) : V) ev = sUseHorn ((fIdx_{name} : ℕ) : V) ev (vecOf row_{name}_as) row_{name}_c := by')
        E(f'  rw [mkStep, frag1Pieces_{name}]')
        E(f'  simp [fpiece_{name}, sUseHorn]')
        E('')
        E(f'lemma ftag_{name} {{W : V}} (hWp : W = frag1Pieces) (ev : V) : sTag (mkStep W ({idx} : V) ev) = 0 := by')
        E(f'  subst hWp')
        E(f'  have hk : ((fIdx_{name} : ℕ) : V) = ({idx} : V) := by simp [fIdx_{name}]')
        E(f'  rw [← hk, fmk_{name}]; simp')
    E('')
E('/-! ### The per-row applicability lemmas `fok_<row>` (at `M = 8`, or `M = 9` for the nine-witness rows) -/')
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
    E(f'lemma fok_{name} {{tbl N E Γ W : V}} {binders}(htbl : TableOK tbl N) (hF : Frag1Table tbl) (hWp : W = frag1Pieces)')
    E(f'    (hΓ : IsFormulaSet LAct Γ) {hyps} {mems} :')
    E(f'    StepOK tbl E (({Mcap} : ℕ) : V) Γ (mkStep W {idx} {vec}) ∧ sTag (mkStep W {idx} {vec}) = {tag} ∧')
    E(f'    ctxAfter Γ (mkStep W {idx} {vec}) = {after} := by')
    E(f'  subst hWp')
    E(f'  have hk : ((fIdx_{name} : ℕ) : V) = ({idx} : V) := by simp [fIdx_{name}]')
    E(f'  have hstep := fmk_{name} (V := V) {vec}')
    E(f'  have hlen := frag1Table_len hF fIdx_{name} (by decide)')
    E(f'  have hrow := frag1Table_{name} hF')
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

# ---- the layout rows Frag1 uses, transferred to the fragment pieces
LAYOUT_USED = ['eqRefl', 'eqSymm', 'insertTotalC', 'memInsertSelfC', 'subsetInsertC', 'subsetTransC', 'subsetMemC',
               'emptySubsetC', 'isFormulaSetInsertC', 'fsetSigmaPiC', 'setLenTotalC', 'subsetReflC', 'subsetAntisymm',
               'congMem']
layout = open('ArithS/Necessitation/Layout.lean').read()
E('/-! ### The layout rows Frag1 uses, read from the fragment pieces (`flok_<row>` from `lok_<row>`) -/')
E('')
for name in LAYOUT_USED:
    li = layout.index('lemma lok_%s ' % name)
    stmt = layout[li: layout.index(':= by', li)]
    idxm = re.search(r'def lIdx_%s : ℕ := (\d+)' % name, layout)
    idx = int(idxm.group(1))
    # the statement: replace the head and the table hypothesis; keep binders/hypotheses verbatim
    head, rest = stmt.split('(htbl : TableOK tbl N) (hL : LayoutTable tbl) (hWp : W = layoutPieces)', 1)
    head = head.replace('lemma lok_%s' % name, 'lemma flok_%s' % name)
    E(head + '(htbl : TableOK tbl N) (hF : Frag1Table tbl) (hWp : W = frag1Pieces)' + rest + ':= by')
    E('  subst hWp')
    E(f'  have e : ∀ ev : V, mkStep frag1Pieces ({idx} : V) ev = mkStep layoutPieces ({idx} : V) ev := fun ev ↦ by')
    E(f'    have := mkStep_frag1Pieces_lt {idx} (by decide) ev; simpa using this')
    E('  rw [e]')
    args = re.findall(r'\((h[A-Za-zΓ0-9₀₁₂₃₄₅₆₇₈₉\']*) :', rest)
    E(f'  exact lok_{name} htbl hF.layoutTable rfl {" ".join(args)}')
    E('')
E('end frag1Table')

head = '''import ArithS.Necessitation.Layout
import ArithS.Necessitation.NumSteps

/-!
# ArithS.Necessitation.Frag1Rows — the fragment table (GENERATED by `arith/scripts/gen_frag1.py`)

1. The rows the six re-description-free fragments use, re-issued with their `quote_row_`/`inst_` lemmas
   (the originals in `Lib/Nodes.lean`, `Lib/Occ.lean`, `Lib/Lengths.lean`, `Lib/Sets.lean`, `Lib/Formulas.lean`
   have none; blocks produced by `gen_frag.py`'s `gen_row`, same names, same DSL): the totalities
   `tot<Tag>`, the `intro<Tag>` and `dlen<Tag>` node rows for `axL`, `verumIntro`, `andIntro`, `orIntro`,
   `wkRule`, `cutRule`; the bounds `dlenLeafLe/dlenUnaryLe/dlenBinaryLe`, `leAddLeAdd`, `leRefl`, `leTrans`,
   `setLenInsertLe`; the set rows `insertSubset`, `memInsertOfMem`, `insertEqOfMem` (`negTotal` is a walk
   row of `RowInst`, entered in the table only).
2. The fragment table: `frag1Rows := layoutRows ++ frag1ExtraRows` — the 87 layout rows at their indices, then
   the rows above and the `fstIdx<Tag>`/congruence rows of `RowInstB` at `fIdx_<row> = 87 + k`. `Frag1Table tbl`
   (implies `LayoutTable tbl`), `exists_frag1Table`, the piece table `frag1Pieces` extending `layoutPieces`
   entrywise (`mkStep_frag1Pieces_lt`), and per row `frag1Table_<row>`, `fmk_<row>`, `ftag_<row>`, `fok_<row>`
   (the step is applicable at `M = 8` — `M = 9` for the nine-witness rows `introAnd`/`dlenAnd` — and its
   `ctxAfter` inserts the canonical fact), plus `flok_<row>`: the layout rows Frag1 uses, read from `frag1Pieces`.
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

/-! ## 1. The rows, re-issued -/

section frag1Rows

'''
open('ArithS/Necessitation/Frag1Rows.lean','w').write(head + new_blocks + '\nend frag1Rows\n\n' + '\n'.join(o) + '\n\nend ArithS\n')
print('rows', len(TABLE))
