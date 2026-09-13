#!/usr/bin/env python3
"""Generator for the FRAGMENT rows of `DESIGN_fragments.md` §8.1 (2026-09-13):

    python3 arith/scripts/gen_frag.py arith/ArithS/Necessitation/Lib/Frag.lean arith/ArithS/Necessitation/RowInstB.lean [groups]

reads the hand-written headers `Frag.lean.head` and `RowInstB.lean.head` next to this script and writes

* `Lib/Frag.lean` — for every row `x`: `xB : ArithmeticSemisentence m` (the DSL body, binders in
  index order), `x := ∀¹* xB`, `models_x` (one `simp`), `pa_proves_x` (the per-row proof term of the
  table), `lib_x`;
* `RowInstB.lean` — the predicate codes `P…`/fact codes `…Fact` the rows need that `RowInst.lean`/
  `Chain.lean` do not define, and for every row the `quote_row_x`/`isSemiformula_x_as/_c`/`inst_x`
  lemmas in `RowInst.lean`'s style (the `gen_rowinst.py` machinery, extended to `+`/`*` entries).

Row table: (group, name, binders (DSL order, x0 = #0), antecedents [(pred, args)], conclusion,
proof, doc).  Args (entry AST): a binder/existential variable name, 'Z'/'One'/'Two' for the literals
`0`/`1`/`2`, ('S', e) for `e + 1`, ('C', k) for the chain literal `0 + 1 + ... + 1` (cT k),
('P', a, b) for `a + b`, ('M', a, b) for `a * b`.
Conclusion: ('atom', pred, args) | ('ex', [vars], [conjuncts]).  `proof` is the Lean term after
`models_x.mpr` (a `fun` over the binders and the antecedents); `None` = the default
`by subst_vars; first | rfl | assumption | trivial`.
The one optional argument restricts the generation to a comma-separated list of groups, each
optionally sliced `group@start-end` (row positions inside the group, end exclusive).
"""
import sys

# ----------------------------------------------------------------------------- predicates
# key -> dict(dsl: args -> DSL atom text, sem: Lean semisentence (for the P code), ar, P, F, args,
#             V: args -> the V-level reading, simps: extra simp lemmas for `models_`,
#             have: what already exists {'P','isSem','shift','fvOcc','Fdef','isFormula','shiftF','len','occ'},
#             unfold: extra names to unfold in `quote_row` (e.g. the sentence behind the code))
ALL = {'P', 'isSem', 'shift', 'fvOcc', 'Fdef', 'isFormula', 'shiftF', 'len', 'occ'}
CHAIN = {'P', 'isSem', 'Fdef', 'isFormula'}

def graph(sem, ar, P, F, args, dslname, Vfun, simps=(), have=frozenset(), unfold=()):
    return dict(dsl=lambda a: f'!{dslname} ' + ' '.join(a), sem=sem, ar=ar, P=P, F=F, args=args,
                V=Vfun, simps=list(simps), have=set(have), unfold=list(unfold))

PREDS = {
  # ---- existing in RowInst / Steps
  'pi':      graph('(↑(isSemiformula LAct).pi : ArithmeticSemisentence 2)', 2, 'Ppi', 'piFact', ['n', 'a'],
                   '(isSemiformula LAct).pi', lambda a: f'IsSemiformula LAct {a[0]} {a[1]}', have=ALL),
  'sigma':   graph('(↑(isSemiformula LAct).sigma : ArithmeticSemisentence 2)', 2, 'Psigma', 'sigmaFact', ['n', 'a'],
                   '(isSemiformula LAct).sigma', lambda a: f'IsSemiformula LAct {a[0]} {a[1]}', have=ALL),
  'qqAnd':   graph('(↑qqAndDef : ArithmeticSemisentence 3)', 3, 'Pand', 'andFact', ['z', 'a', 'b'],
                   'qqAndDef', lambda a: f'{a[0]} = {a[1]} ^⋏ {a[2]}', have=ALL),
  'qqOr':    graph('(↑qqOrDef : ArithmeticSemisentence 3)', 3, 'Por', 'orFact', ['z', 'a', 'b'],
                   'qqOrDef', lambda a: f'{a[0]} = {a[1]} ^⋎ {a[2]}', have=ALL),
  'qqAll':   graph('(↑qqAllDef : ArithmeticSemisentence 2)', 2, 'Pall', 'allFact', ['q', 'p'],
                   'qqAllDef', lambda a: f'{a[0]} = ^∀ {a[1]}', have=ALL),
  'qqExs':   graph('(↑qqExsDef : ArithmeticSemisentence 2)', 2, 'Pexs', 'exsFact', ['q', 'p'],
                   'qqExsDef', lambda a: f'{a[0]} = ^∃ {a[1]}', have=ALL),
  'qqRel':   graph('(↑qqRelDef : ArithmeticSemisentence 4)', 4, 'Prel', 'relFact', ['p', 'k', 'R', 'v'],
                   'qqRelDef', lambda a: f'{a[0]} = ^rel {a[1]} {a[2]} {a[3]}', have=ALL),
  'qqNRel':  graph('(↑qqNRelDef : ArithmeticSemisentence 4)', 4, 'Pnrel', 'nrelFact', ['p', 'k', 'R', 'v'],
                   'qqNRelDef', lambda a: f'{a[0]} = ^nrel {a[1]} {a[2]} {a[3]}', have=ALL),
  'qqVerum': graph('(↑qqVerumDef : ArithmeticSemisentence 1)', 1, 'Pverum', 'verumFact', ['p'],
                   'qqVerumDef', lambda a: f'{a[0]} = ^⊤', have=ALL),
  'qqFalsum':graph('(↑qqFalsumDef : ArithmeticSemisentence 1)', 1, 'Pfalsum', 'falsumFact', ['p'],
                   'qqFalsumDef', lambda a: f'{a[0]} = ^⊥', have=ALL),
  'qqFunc':  graph('(↑qqFuncDef : ArithmeticSemisentence 4)', 4, 'Pfunc', 'funcFact', ['t', 'k', 'f', 'v'],
                   'qqFuncDef', lambda a: f'{a[0]} = ^func {a[1]} {a[2]} {a[3]}', have=ALL),
  'qqBvar':  graph('(↑qqBvarDef : ArithmeticSemisentence 2)', 2, 'Pbvar', 'bvarFact', ['t', 'z'],
                   'qqBvarDef', lambda a: f'{a[0]} = ^#{a[1]}', have=ALL),
  'qqFvar':  graph('(↑qqFvarDef : ArithmeticSemisentence 2)', 2, 'Pfvar', 'fvarFact', ['t', 'x'],
                   'qqFvarDef', lambda a: f'{a[0]} = ^&{a[1]}', have=ALL),
  'adjoin':  graph('(↑adjoinDef : ArithmeticSemisentence 3)', 3, 'Padjoin', 'adjFact', ['w', 't', 'v'],
                   'adjoinDef', lambda a: f'{a[0]} = {a[1]} ∷ {a[2]}', have=ALL),
  'tpi':     graph('(↑(isSemiterm LAct).pi : ArithmeticSemisentence 2)', 2, 'PtPi', 'tPiFact', ['n', 't'],
                   '(isSemiterm LAct).pi', lambda a: f'IsSemiterm LAct {a[0]} {a[1]}', have=ALL),
  'tsigma':  graph('(↑(isSemiterm LAct).sigma : ArithmeticSemisentence 2)', 2, 'PtSigma', 'tSigmaFact', ['n', 't'],
                   '(isSemiterm LAct).sigma', lambda a: f'IsSemiterm LAct {a[0]} {a[1]}', have=ALL),
  'tvpi':    graph('(↑(isSemitermVec LAct).pi : ArithmeticSemisentence 3)', 3, 'PtvPi', 'tvPiFact', ['k', 'n', 'v'],
                   '(isSemitermVec LAct).pi', lambda a: f'IsSemitermVec LAct {a[0]} {a[1]} {a[2]}', have=ALL),
  'tvsigma': graph('(↑(isSemitermVec LAct).sigma : ArithmeticSemisentence 3)', 3, 'PtvSigma', 'tvSigmaFact', ['k', 'n', 'v'],
                   '(isSemitermVec LAct).sigma', lambda a: f'IsSemitermVec LAct {a[0]} {a[1]} {a[2]}', have=ALL),
  'utvpi':   graph('(↑(isUTermVec LAct).pi : ArithmeticSemisentence 2)', 2, 'PutvPi', 'utvPiFact', ['k', 'v'],
                   '(isUTermVec LAct).pi', lambda a: f'IsUTermVec LAct {a[0]} {a[1]}', have=ALL),
  'utvsigma':graph('(↑(isUTermVec LAct).sigma : ArithmeticSemisentence 2)', 2, 'PutvSigma', 'utvSigmaFact', ['k', 'v'],
                   '(isUTermVec LAct).sigma', lambda a: f'IsUTermVec LAct {a[0]} {a[1]}', have=ALL),
  'isRel':   graph('(↑LAct.isRel : ArithmeticSemisentence 2)', 2, 'PisRel', 'isRelFact', ['k', 'R'],
                   'LAct.isRel', lambda a: f'LAct.IsRel {a[0]} {a[1]}', have=ALL),
  'isFunc':  graph('(↑LAct.isFunc : ArithmeticSemisentence 2)', 2, 'PisFunc', 'isFuncFact', ['k', 'f'],
                   'LAct.isFunc', lambda a: f'LAct.IsFunc {a[0]} {a[1]}', have=ALL),
  'lt':      dict(dsl=lambda a: f'{a[0]} < {a[1]}',
                  sem='(Rewriting.emb (Semiformula.Operator.LT.lt : Semiformula.Operator ℒₒᵣ 2).sentence : ArithmeticSemisentence 2)',
                  ar=2, P='Plt', F='ltFact', args=['a', 'b'], V=lambda a: f'{a[0]} < {a[1]}', simps=[], have=set(ALL), unfold=[]),
  'negG':    graph('(↑(negGraph LAct) : ArithmeticSemisentence 2)', 2, 'PnegG', 'negFact', ['y', 'p'],
                   '(negGraph LAct)', lambda a: f'{a[0]} = neg LAct {a[1]}', have=ALL),
  'shiftG':  graph('(↑(shiftGraph LAct) : ArithmeticSemisentence 2)', 2, 'PshiftG', 'shiftFact', ['y', 'p'],
                   '(shiftGraph LAct)', lambda a: f'{a[0]} = shift LAct {a[1]}', simps=['shift.defined.iff'], have=ALL),
  'substsG': graph('(↑(substsGraph LAct) : ArithmeticSemisentence 3)', 3, 'PsubstsG', 'substFact', ['y', 'w', 'p'],
                   '(substsGraph LAct)', lambda a: f'{a[0]} = subst LAct {a[1]} {a[2]}', simps=['subst.defined.iff'], have=ALL),
  'substs1G':graph('(↑(substs1Graph LAct) : ArithmeticSemisentence 3)', 3, 'Psubsts1G', 'substs1Fact', ['y', 't', 'p'],
                   '(substs1Graph LAct)', lambda a: f'{a[0]} = substs1 LAct {a[1]} {a[2]}', simps=['substs1.defined.iff'], have=ALL),
  'freeG':   graph('(↑(freeGraph LAct) : ArithmeticSemisentence 2)', 2, 'PfreeG', 'freeFact', ['y', 'p'],
                   '(freeGraph LAct)', lambda a: f'{a[0]} = free LAct {a[1]}', simps=['free.defined.iff'], have=ALL),
  'qVecG':   graph('(↑(qVecGraph LAct) : ArithmeticSemisentence 2)', 2, 'PqVecG', 'qVecFact', ['u', 'w'],
                   '(qVecGraph LAct)', lambda a: f'{a[0]} = qVec LAct {a[1]}', simps=['qVec.defined.iff'], have=ALL),
  'tsvG':    graph('(↑(termSubstVecGraph LAct) : ArithmeticSemisentence 4)', 4, 'PtsvG', 'tsvFact', ['u', 'k', 'w', 'v'],
                   '(termSubstVecGraph LAct)', lambda a: f'{a[0]} = termSubstVec LAct {a[1]} {a[2]} {a[3]}',
                   simps=['termSubstVec.defined.iff'], have=ALL),
  'tshvG':   graph('(↑(termShiftVecGraph LAct) : ArithmeticSemisentence 3)', 3, 'PtshvG', 'tshvFact', ['u', 'k', 'v'],
                   '(termShiftVecGraph LAct)', lambda a: f'{a[0]} = termShiftVec LAct {a[1]} {a[2]}',
                   simps=['termShiftVec.defined.iff'], have=ALL),
  # ---- existing in Chain (P, isSemiformula, fact def, isFormula; the rest generated here)
  'deriv':   graph('(↑(derivation TAct).sigma : ArithmeticSemisentence 1)', 1, 'Pderiv', 'derFact', ['e'],
                   '(derivation TAct).sigma', lambda a: f'Derivation TAct {a[0]}', have=CHAIN, unfold=['derivS']),
  'fstIdx':  graph('(↑fstIdxDef : ArithmeticSemisentence 2)', 2, 'PfstIdx', 'fstIdxFact', ['s', 'e'],
                   'fstIdxDef', lambda a: f'{a[0]} = fstIdx {a[1]}', have=CHAIN, unfold=['fstIdxS']),
  'dlen':    graph('(↑(dlenGraphDef LAct).sigma : ArithmeticSemisentence 2)', 2, 'Pdlen', 'dlenFact', ['e', 'n'],
                   '(dlenGraphDef LAct).sigma', lambda a: f'DlenGraph LAct {a[0]} {a[1]}', have=CHAIN, unfold=['dlenS']),
  'le':      dict(dsl=lambda a: f'{a[0]} ≤ {a[1]}',
                  sem='(Rewriting.emb (Semiformula.Operator.LE.le : Semiformula.Operator ℒₒᵣ 2).sentence : ArithmeticSemisentence 2)',
                  ar=2, P='Ple', F='leFact', args=['n', 'u'], V=lambda a: f'{a[0]} ≤ {a[1]}', simps=[], have=set(CHAIN), unfold=['leS']),
  # ---- new
  'eq':      dict(dsl=lambda a: f'{a[0]} = {a[1]}',
                  sem='(Rewriting.emb (Semiformula.Operator.Eq.eq : Semiformula.Operator ℒₒᵣ 2).sentence : ArithmeticSemisentence 2)',
                  ar=2, P='Peq', F='eqFact', args=['a', 'b'], V=lambda a: f'{a[0]} = {a[1]}', simps=[], have=set(), unfold=[]),
  'mem':     dict(dsl=lambda a: f'{a[0]} ∈ {a[1]}',
                  sem='(Rewriting.emb (Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₒᵣ 2).sentence : ArithmeticSemisentence 2)',
                  ar=2, P='Pmem', F='memFact', args=['x', 's'], V=lambda a: f'{a[0]} ∈ {a[1]}', simps=[], have=set(), unfold=[]),
  'insert':  graph('(↑insertDef : ArithmeticSemisentence 3)', 3, 'Pinsert', 'insFact', ['t', 'x', 's'],
                   'insertDef', lambda a: f'{a[0]} = insert {a[1]} {a[2]}'),
  'subset':  graph('(↑bitSubsetDef : ArithmeticSemisentence 2)', 2, 'Psubset', 'subsetFact', ['s', 't'],
                   'bitSubsetDef', lambda a: f'{a[0]} ⊆ {a[1]}'),
  'fsetPi':  graph('(↑(isFormulaSet LAct).pi : ArithmeticSemisentence 1)', 1, 'PfsetPi', 'fsetPiFact', ['s'],
                   '(isFormulaSet LAct).pi', lambda a: f'IsFormulaSet LAct {a[0]}'),
  'fsetSigma': graph('(↑(isFormulaSet LAct).sigma : ArithmeticSemisentence 1)', 1, 'PfsetSigma', 'fsetSigmaFact', ['s'],
                   '(isFormulaSet LAct).sigma', lambda a: f'IsFormulaSet LAct {a[0]}'),
  'ufPi':    graph('(↑(isUFormula LAct).pi : ArithmeticSemisentence 1)', 1, 'PufPi', 'ufPiFact', ['p'],
                   '(isUFormula LAct).pi', lambda a: f'IsUFormula LAct {a[0]}'),
  'setShiftG': graph('(↑(setShiftGraph LAct) : ArithmeticSemisentence 2)', 2, 'PsetShiftG', 'setShiftFact', ['t', 's'],
                   '(setShiftGraph LAct)', lambda a: f'{a[0]} = setShift LAct {a[1]}', simps=['setShift.defined.iff']),
  'setLen':  graph('(↑(setLenDef LAct) : ArithmeticSemisentence 2)', 2, 'PsetLen', 'setLenFact', ['l', 's'],
                   '(setLenDef LAct)', lambda a: f'{a[0]} = setLen LAct {a[1]}', simps=['setLen_defined.iff']),
  'flenG':   graph('(↑(formulaLenGraph LAct) : ArithmeticSemisentence 2)', 2, 'PflenG', 'lenFact', ['l', 'p'],
                   '(formulaLenGraph LAct)', lambda a: f'{a[0]} = formulaLen LAct {a[1]}', simps=['formulaLen.defined.iff']),
  'tlenG':   graph('(↑(termLenGraph LAct) : ArithmeticSemisentence 2)', 2, 'PtlenG', 'tlenFact', ['l', 't'],
                   '(termLenGraph LAct)', lambda a: f'{a[0]} = termLen LAct {a[1]}', simps=['termLen.defined.iff']),
  'tlvG':    graph('(↑(termLenVecGraph LAct) : ArithmeticSemisentence 3)', 3, 'PtlvG', 'tlvFact', ['M', 'k', 'v'],
                   '(termLenVecGraph LAct)', lambda a: f'{a[0]} = termLenVec LAct {a[1]} {a[2]}', simps=['termLenVec.defined.iff']),
  'listSum': graph('(↑listSumDef : ArithmeticSemisentence 2)', 2, 'PlistSum', 'listSumFact', ['s', 'M'],
                   'listSumDef', lambda a: f'{a[0]} = listSum {a[1]}', simps=['listSum_defined.iff']),
  'tshG':    graph('(↑(termShiftGraph LAct) : ArithmeticSemisentence 2)', 2, 'PtshG', 'tshFact', ['t2', 't'],
                   '(termShiftGraph LAct)', lambda a: f'{a[0]} = termShift LAct {a[1]}', simps=['termShift.defined.iff']),
  'tsG':     graph('(↑(termSubstGraph LAct) : ArithmeticSemisentence 3)', 3, 'PtsG', 'tsFact', ['e', 'w', 't'],
                   '(termSubstGraph LAct)', lambda a: f'{a[0]} = termSubst LAct {a[1]} {a[2]}', simps=['termSubst.defined.iff']),
  'tbshG':   graph('(↑(termBShiftGraph LAct) : ArithmeticSemisentence 2)', 2, 'PtbshG', 'tbshFact', ['e2', 'e'],
                   '(termBShiftGraph LAct)', lambda a: f'{a[0]} = termBShift LAct {a[1]}', simps=['termBShift.defined.iff']),
  'tbshvG':  graph('(↑(termBShiftVecGraph LAct) : ArithmeticSemisentence 3)', 3, 'PtbshvG', 'tbshvFact', ['u', 'k', 'v'],
                   '(termBShiftVecGraph LAct)', lambda a: f'{a[0]} = termBShiftVec LAct {a[1]} {a[2]}', simps=['termBShiftVec.defined.iff']),
  'nth':     graph('(↑nthDef : ArithmeticSemisentence 3)', 3, 'Pnth', 'nthFact', ['e', 'w', 'i'],
                   'nthDef', lambda a: f'{a[0]} = {a[1]}.[{a[2]}]', simps=['nth_defined.iff']),
  'alls':    graph('(↑qqAllsDef : ArithmeticSemisentence 3)', 3, 'Palls', 'allsFact', ['p', 'b', 'm'],
                   'qqAllsDef', lambda a: f'{a[0]} = qqAlls {a[1]} {a[2]}', simps=['qqAlls_defined.iff']),
  'bvG':     graph('(↑(bvGraph LAct) : ArithmeticSemisentence 2)', 2, 'PbvG', 'bvFact', ['m', 'b'],
                   '(bvGraph LAct)', lambda a: f'{a[0]} = Bootstrapping.bv LAct {a[1]}', simps=['bv.defined.iff']),
  'termBVG': graph('(↑(termBVGraph LAct) : ArithmeticSemisentence 2)', 2, 'PtermBVG', 'termBVFact', ['m', 't'],
                   '(termBVGraph LAct)', lambda a: f'{a[0]} = termBV LAct {a[1]}', simps=['termBV.defined.iff']),
  'termBVVecG': graph('(↑(termBVVecGraph LAct) : ArithmeticSemisentence 3)', 3, 'PtermBVVecG', 'termBVVecFact', ['M', 'k', 'v'],
                   '(termBVVecGraph LAct)', lambda a: f'{a[0]} = termBVVec LAct {a[1]} {a[2]}', simps=['termBVVec.defined.iff']),
  'listMax': graph('(↑listMaxDef : ArithmeticSemisentence 2)', 2, 'PlistMax', 'listMaxFact', ['m', 'M'],
                   'listMaxDef', lambda a: f'{a[0]} = listMax {a[1]}', simps=['listMax_defined.iff']),
  'maxG':    graph('(↑max.dfn : ArithmeticSemisentence 3)', 3, 'PmaxG', 'maxFact', ['m', 'a', 'b'],
                   'max.dfn', lambda a: f'{a[0]} = max {a[1]} {a[2]}'),
  'subG':    graph('(↑subDef : ArithmeticSemisentence 3)', 3, 'PsubG', 'subDFact', ['m', 'a', 'b'],
                   'subDef', lambda a: f'{a[0]} = {a[1]} - {a[2]}'),
  'fvarVec': graph('(↑fvarVecDef : ArithmeticSemisentence 2)', 2, 'PfvarVec', 'fvarVecFact', ['fv', 'm'],
                   'fvarVecDef', lambda a: f'{a[0]} = fvarVec {a[1]}', simps=['fvarVec_defined.iff']),
  'length':  graph('(↑lengthDef : ArithmeticSemisentence 2)', 2, 'Plength', 'lengthFact', ['l', 'k'],
                   'lengthDef', lambda a: f'{a[0]} = ‖{a[1]}‖', simps=['length_defined.iff']),
  'bnumG':   graph('(↑bnumGraph : ArithmeticSemisentence 2)', 2, 'Pbnum', 'bnumFact', ['t', 'k'],
                   'bnumGraph', lambda a: f'{a[0]} = bnum {a[1]}', simps=['bnum.defined.iff']),
  'qqAddG':  graph('(↑qqAddGraph : ArithmeticSemisentence 3)', 3, 'PqqAdd', 'qqAddFact', ['u', 'a', 'b'],
                   'qqAddGraph', lambda a: f'{a[0]} = {a[1]} ^+ {a[2]}', simps=['qqAdd_defined.iff']),
  'qqMulG':  graph('(↑qqMulGraph : ArithmeticSemisentence 3)', 3, 'PqqMul', 'qqMulFact', ['u', 'a', 'b'],
                   'qqMulGraph', lambda a: f'{a[0]} = {a[1]} ^* {a[2]}', simps=['qqMul_defined.iff']),
  'dlenDef': graph('(↑(dlenDef TAct) : ArithmeticSemisentence 2)', 2, 'PdlenDef', 'dlenDefFact', ['n', 'd'],
                   '(dlenDef TAct)', lambda a: f'{a[0]} = dlen TAct {a[1]}', simps=['dlen_defined.iff']),
  'proof':   graph('(↑(proof TAct).sigma : ArithmeticSemisentence 2)', 2, 'Pproof', 'proofFact', ['d', 'g'],
                   '(proof TAct).sigma', lambda a: f'Proof TAct {a[0]} {a[1]}'),
  'instBG':  graph('(↑instBGraph : ArithmeticSemisentence 3)', 3, 'PinstB', 'instBFact', ['g', 'n', 'k'],
                   'instBGraph', lambda a: f'{a[0]} = instB {a[1]} {a[2]}', simps=['instB.defined.iff']),
  'gG':      graph('(↑gGraph : ArithmeticSemisentence 2)', 2, 'Pg', 'gFact', ['a', 'k'],
                   'gGraph', lambda a: f'{a[0]} = gBudget {a[1]}', simps=['gBudget.defined.iff']),
  # ---- node graphs
  'axL':     graph('(↑axLGraph : ArithmeticSemisentence 3)', 3, 'PaxL', 'axLFact', ['e', 's', 'p'],
                   'axLGraph', lambda a: f'{a[0]} = axL {a[1]} {a[2]}'),
  'verumIntro': graph('(↑verumIntroGraph : ArithmeticSemisentence 2)', 2, 'PverumIntro', 'verumIntroFact', ['e', 's'],
                   'verumIntroGraph', lambda a: f'{a[0]} = verumIntro {a[1]}'),
  'andIntro': graph('(↑andIntroGraph : ArithmeticSemisentence 6)', 6, 'PandIntro', 'andIntroFact', ['e', 's', 'p', 'q', 'dp', 'dq'],
                   'andIntroGraph', lambda a: f'{a[0]} = andIntro {a[1]} {a[2]} {a[3]} {a[4]} {a[5]}'),
  'orIntro': graph('(↑orIntroGraph : ArithmeticSemisentence 5)', 5, 'PorIntro', 'orIntroFact', ['e', 's', 'p', 'q', 'd'],
                   'orIntroGraph', lambda a: f'{a[0]} = orIntro {a[1]} {a[2]} {a[3]} {a[4]}'),
  'allIntro': graph('(↑allIntroGraph : ArithmeticSemisentence 4)', 4, 'PallIntro', 'allIntroFact', ['e', 's', 'p', 'd'],
                   'allIntroGraph', lambda a: f'{a[0]} = allIntro {a[1]} {a[2]} {a[3]}'),
  'exsIntro': graph('(↑exsIntroGraph : ArithmeticSemisentence 5)', 5, 'PexsIntro', 'exsIntroFact', ['e', 's', 'p', 't', 'd'],
                   'exsIntroGraph', lambda a: f'{a[0]} = exsIntro {a[1]} {a[2]} {a[3]} {a[4]}'),
  'wkRule':  graph('(↑wkRuleGraph : ArithmeticSemisentence 3)', 3, 'PwkRule', 'wkRuleFact', ['e', 's', 'd'],
                   'wkRuleGraph', lambda a: f'{a[0]} = wkRule {a[1]} {a[2]}'),
  'shiftRule': graph('(↑shiftRuleGraph : ArithmeticSemisentence 3)', 3, 'PshiftRule', 'shiftRuleFact', ['e', 's', 'd'],
                   'shiftRuleGraph', lambda a: f'{a[0]} = shiftRule {a[1]} {a[2]}'),
  'cutRule': graph('(↑cutRuleGraph : ArithmeticSemisentence 5)', 5, 'PcutRule', 'cutRuleFact', ['e', 's', 'p', 'd1', 'd2'],
                   'cutRuleGraph', lambda a: f'{a[0]} = cutRule {a[1]} {a[2]} {a[3]} {a[4]}'),
  'axm':     graph('(↑axmGraph : ArithmeticSemisentence 3)', 3, 'Paxm', 'axmFact', ['e', 's', 'p'],
                   'axmGraph', lambda a: f'{a[0]} = axm {a[1]} {a[2]}'),
}

def A(pred, *args):
    return ('atom', pred, list(args))
def EX(vs, conj):
    return ('ex', vs, conj)
S = lambda v: ('S', v)
C = lambda k: ('C', k)
P = lambda a, b: ('P', a, b)
M = lambda a, b: ('M', a, b)

DEFAULT = None  # `by subst_vars; first | rfl | assumption | trivial`

def by(tac):
    return ('by', tac)

# ----------------------------------------------------------------------------- the rows
# (group, name, binders, ants, conc, proof, doc)
ROWS = []
def row(group, name, binders, ants, conc, proof=DEFAULT, doc=''):
    ROWS.append((group, name, binders, ants, conc, proof, doc))

# ===== A. copy-in: equality and the congruence rows (`DESIGN_fragments.md` §3.3)
row('copy', 'eqTotal', ['x'], [], EX(['y'], [A('eq', 'y', 'x')]), 'fun _ ↦ ⟨_, rfl⟩',
    '`∀ x, ∃ y, y = x` — a fresh eigenvariable equal to a known object (the copy step).')
row('copy', 'eqRefl', ['x'], [], A('eq', 'x', 'x'), 'fun _ ↦ rfl', '`x = x`.')
row('copy', 'eqSymm', ['y', 'x'], [A('eq', 'x', 'y')], A('eq', 'y', 'x'), 'fun _ _ h ↦ h.symm', '`x = y → y = x`.')
row('copy', 'eqTrans', ['z', 'y', 'x'], [A('eq', 'x', 'y'), A('eq', 'y', 'z')], A('eq', 'x', 'z'),
    'fun _ _ _ h₁ h₂ ↦ h₁.trans h₂', '`x = y → y = z → x = z`.')
row('copy', 'congPi', ['y', 'x', 'n'], [A('eq', 'y', 'x'), A('pi', 'n', 'x')], A('sigma', 'n', 'y'),
    doc='`y = x → IsSemiformula n x → IsSemiformula n y`.')
row('copy', 'congTPi', ['y', 'x', 'n'], [A('eq', 'y', 'x'), A('tpi', 'n', 'x')], A('tsigma', 'n', 'y'),
    doc='`y = x → IsSemiterm n x → IsSemiterm n y`.')
row('copy', 'congTvPi', ['y', 'x', 'n', 'k'], [A('eq', 'y', 'x'), A('tvpi', 'k', 'n', 'x')], A('tvsigma', 'k', 'n', 'y'),
    doc='`y = x → IsSemitermVec k n x → IsSemitermVec k n y`.')
row('copy', 'congUtvPi', ['y', 'x', 'k'], [A('eq', 'y', 'x'), A('utvpi', 'k', 'x')], A('utvsigma', 'k', 'y'),
    doc='`y = x → IsUTermVec k x → IsUTermVec k y`.')
row('copy', 'congUfPi', ['y', 'x'], [A('eq', 'y', 'x'), A('ufPi', 'x')], A('ufPi', 'y'),
    doc='`y = x → IsUFormula x → IsUFormula y` (`.pi` on both sides: the recognizer consumes `.pi`).')
row('copy', 'congAnd', ["q'", "p'", "r'", 'q', 'p', 'r'],
    [A('eq', "r'", 'r'), A('eq', "p'", 'p'), A('eq', "q'", 'q'), A('qqAnd', 'r', 'p', 'q')], A('qqAnd', "r'", "p'", "q'"),
    doc="`r' = r → p' = p → q' = q → r = p ⋏ q → r' = p' ⋏ q'` (all arguments at once).")
row('copy', 'congOr', ["q'", "p'", "r'", 'q', 'p', 'r'],
    [A('eq', "r'", 'r'), A('eq', "p'", 'p'), A('eq', "q'", 'q'), A('qqOr', 'r', 'p', 'q')], A('qqOr', "r'", "p'", "q'"),
    doc="the `⋎` congruence.")
row('copy', 'congAll', ["p'", "q'", 'p', 'q'], [A('eq', "q'", 'q'), A('eq', "p'", 'p'), A('qqAll', 'q', 'p')], A('qqAll', "q'", "p'"),
    doc="the `∀` congruence.")
row('copy', 'congExs', ["p'", "q'", 'p', 'q'], [A('eq', "q'", 'q'), A('eq', "p'", 'p'), A('qqExs', 'q', 'p')], A('qqExs', "q'", "p'"),
    doc="the `∃` congruence.")
row('copy', 'congRel', ["v'", "r'", 'v', 'R', 'k', 'r'],
    [A('eq', "r'", 'r'), A('eq', "v'", 'v'), A('qqRel', 'r', 'k', 'R', 'v')], A('qqRel', "r'", 'k', 'R', "v'"),
    doc="the `rel` congruence (the symbol numerals are shared).")
row('copy', 'congNRel', ["v'", "r'", 'v', 'R', 'k', 'r'],
    [A('eq', "r'", 'r'), A('eq', "v'", 'v'), A('qqNRel', 'r', 'k', 'R', 'v')], A('qqNRel', "r'", 'k', 'R', "v'"),
    doc="the `nrel` congruence.")
row('copy', 'congVerum', ["p'", 'p'], [A('eq', "p'", 'p'), A('qqVerum', 'p')], A('qqVerum', "p'"), doc="the `⊤` congruence.")
row('copy', 'congFalsum', ["p'", 'p'], [A('eq', "p'", 'p'), A('qqFalsum', 'p')], A('qqFalsum', "p'"), doc="the `⊥` congruence.")
row('copy', 'congFunc', ["v'", "t'", 'v', 'f', 'k', 't'],
    [A('eq', "t'", 't'), A('eq', "v'", 'v'), A('qqFunc', 't', 'k', 'f', 'v')], A('qqFunc', "t'", 'k', 'f', "v'"),
    doc="the `func` congruence.")
row('copy', 'congBvar', ["t'", 't', 'z'], [A('eq', "t'", 't'), A('qqBvar', 't', 'z')], A('qqBvar', "t'", 'z'), doc="the `#z` congruence.")
row('copy', 'congFvar', ["t'", 't', 'x'], [A('eq', "t'", 't'), A('qqFvar', 't', 'x')], A('qqFvar', "t'", 'x'), doc="the `&x` congruence.")
row('copy', 'congAdj', ["w'", "v'", "t'", 'w', 'v', 't'],
    [A('eq', "w'", 'w'), A('eq', "t'", 't'), A('eq', "v'", 'v'), A('adjoin', 'w', 't', 'v')], A('adjoin', "w'", "t'", "v'"),
    doc="the `∷` congruence.")
row('copy', 'congLen', ['y', 'x', 'l'], [A('eq', 'y', 'x'), A('flenG', 'l', 'x')], A('flenG', 'l', 'y'),
    doc="`y = x → formulaLen x = l → formulaLen y = l`.")
row('copy', 'congTLen', ['y', 'x', 'l'], [A('eq', 'y', 'x'), A('tlenG', 'l', 'x')], A('tlenG', 'l', 'y'),
    doc="`y = x → termLen x = l → termLen y = l`.")
row('copy', 'congLenNum', ["l'", 'l', 'y'], [A('eq', 'l', "l'"), A('flenG', 'l', 'y')], A('flenG', "l'", 'y'),
    doc="`l = l' → formulaLen y = l → formulaLen y = l'` (the numeral into the graph position, §3.6).")
row('copy', 'congTLenNum', ["l'", 'l', 't'], [A('eq', 'l', "l'"), A('tlenG', 'l', 't')], A('tlenG', "l'", 't'),
    doc="the term-length twin of `congLenNum`.")
row('copy', 'congMem', ['s', 'y', 'x'], [A('eq', 'y', 'x'), A('mem', 'x', 's')], A('mem', 'y', 's'),
    doc="`y = x → x ∈ s → y ∈ s`.")
row('copy', 'congMemSet', ["s'", 's', 'x'], [A('eq', "s'", 's'), A('mem', 'x', 's')], A('mem', 'x', "s'"),
    doc="`s' = s → x ∈ s → x ∈ s'`.")
row('copy', 'congFstIdx', ["t'", 't', 'd'], [A('eq', "t'", 't'), A('fstIdx', 't', 'd')], A('fstIdx', "t'", 'd'),
    doc="`t' = t → fstIdx d = t → fstIdx d = t'` (moves a child's goal onto the row's sequent object, §3.4).")
row('copy', 'congSubsetL', ['u', "t'", 't'], [A('eq', "t'", 't'), A('subset', 't', 'u')], A('subset', "t'", 'u'),
    doc="`t' = t → t ⊆ u → t' ⊆ u`.")
row('copy', 'congSubsetR', ["t'", 't', 's'], [A('eq', "t'", 't'), A('subset', 's', 't')], A('subset', 's', "t'"),
    doc="`t' = t → s ⊆ t → s ⊆ t'`.")
row('copy', 'congSetShiftL', ['s', "t'", 't'], [A('eq', "t'", 't'), A('setShiftG', 't', 's')], A('setShiftG', "t'", 's'),
    doc="`t' = t → t = setShift s → t' = setShift s`.")
row('copy', 'congSetShiftR', ["s'", 's', 't'], [A('eq', "s'", 's'), A('setShiftG', 't', 's')], A('setShiftG', 't', "s'"),
    doc="`s' = s → t = setShift s → t = setShift s'`.")
row('copy', 'congShiftL', ['x', "y'", 'y'], [A('eq', "y'", 'y'), A('shiftG', 'y', 'x')], A('shiftG', "y'", 'x'),
    doc="`y' = y → y = shift x → y' = shift x`.")
row('copy', 'congNegL', ['x', "y'", 'y'], [A('eq', "y'", 'y'), A('negG', 'y', 'x')], A('negG', "y'", 'x'),
    doc="`y' = y → y = neg x → y' = neg x`.")
row('copy', 'congSubstArg', ["n'", 'n', 'w', 'y'], [A('eq', 'n', "n'"), A('substsG', 'y', 'w', 'n')], A('substsG', 'y', 'w', "n'"),
    doc="`n = n' → y = subst w n → y = subst w n'` (the top's `congSubstR`, §7.1).")
row('copy', 'congSubstL', ['n', 'w', "y'", 'y'], [A('eq', "y'", 'y'), A('substsG', 'y', 'w', 'n')], A('substsG', "y'", 'w', 'n'),
    doc="`y' = y → y = subst w n → y' = subst w n`.")
row('copy', 'congInsertL', ["t'", 't', 'x', 's'], [A('eq', "t'", 't'), A('insert', 't', 'x', 's')], A('insert', "t'", 'x', 's'),
    doc="`t' = t → t = insert x s → t' = insert x s`.")
row('copy', 'congInsertS', ["s'", 's', 'x', 't'], [A('eq', "s'", 's'), A('insert', 't', 'x', 's')], A('insert', 't', 'x', "s'"),
    doc="`s' = s → t = insert x s → t = insert x s'`.")
row('copy', 'congSetLenR', ['l', "s'", 's'], [A('eq', "s'", 's'), A('setLen', 'l', 's')], A('setLen', 'l', "s'"),
    doc="`s' = s → l = setLen s → l = setLen s'`.")
row('copy', 'congIsFormulaSet', ["s'", 's'], [A('eq', "s'", 's'), A('fsetPi', 's')], A('fsetSigma', "s'"),
    doc="`s' = s → IsFormulaSet s → IsFormulaSet s'`.")

# ===== B. identification: the injectivity rows (§3.5)
row('ident', 'eqOfAnd', ['y', "q'", "p'", 'q', 'p', 'x'],
    [A('qqAnd', 'x', 'p', 'q'), A('qqAnd', 'y', "p'", "q'"), A('eq', 'p', "p'"), A('eq', 'q', "q'")], A('eq', 'x', 'y'),
    doc="`x = p ⋏ q → y = p' ⋏ q' → p = p' → q = q' → x = y`.")
row('ident', 'eqOfOr', ['y', "q'", "p'", 'q', 'p', 'x'],
    [A('qqOr', 'x', 'p', 'q'), A('qqOr', 'y', "p'", "q'"), A('eq', 'p', "p'"), A('eq', 'q', "q'")], A('eq', 'x', 'y'),
    doc="the `⋎` identification.")
row('ident', 'eqOfAll', ['y', "p'", 'p', 'x'], [A('qqAll', 'x', 'p'), A('qqAll', 'y', "p'"), A('eq', 'p', "p'")], A('eq', 'x', 'y'),
    doc="the `∀` identification.")
row('ident', 'eqOfExs', ['y', "p'", 'p', 'x'], [A('qqExs', 'x', 'p'), A('qqExs', 'y', "p'"), A('eq', 'p', "p'")], A('eq', 'x', 'y'),
    doc="the `∃` identification.")
row('ident', 'eqOfRel', ['y', "v'", 'v', 'R', 'k', 'x'],
    [A('qqRel', 'x', 'k', 'R', 'v'), A('qqRel', 'y', 'k', 'R', "v'"), A('eq', 'v', "v'")], A('eq', 'x', 'y'),
    doc="the `rel` identification (the symbol numerals are syntactically shared).")
row('ident', 'eqOfNRel', ['y', "v'", 'v', 'R', 'k', 'x'],
    [A('qqNRel', 'x', 'k', 'R', 'v'), A('qqNRel', 'y', 'k', 'R', "v'"), A('eq', 'v', "v'")], A('eq', 'x', 'y'),
    doc="the `nrel` identification.")
row('ident', 'eqOfVerum', ['y', 'x'], [A('qqVerum', 'x'), A('qqVerum', 'y')], A('eq', 'x', 'y'), doc="the `⊤` identification.")
row('ident', 'eqOfFalsum', ['y', 'x'], [A('qqFalsum', 'x'), A('qqFalsum', 'y')], A('eq', 'x', 'y'), doc="the `⊥` identification.")
row('ident', 'eqOfFunc', ["t'", "v'", 'v', 'f', 'k', 't'],
    [A('qqFunc', 't', 'k', 'f', 'v'), A('qqFunc', "t'", 'k', 'f', "v'"), A('eq', 'v', "v'")], A('eq', 't', "t'"),
    doc="the `func` identification.")
row('ident', 'eqOfBvar', ["t'", 't', 'z'], [A('qqBvar', 't', 'z'), A('qqBvar', "t'", 'z')], A('eq', 't', "t'"),
    doc="the `#z` identification.")
row('ident', 'eqOfFvar', ["t'", 't', 'x'], [A('qqFvar', 't', 'x'), A('qqFvar', "t'", 'x')], A('eq', 't', "t'"),
    doc="the `&x` identification.")
row('ident', 'eqOfAdj', ["w'", "v'", "t'", 'w', 'v', 't'],
    [A('adjoin', 'w', 't', 'v'), A('adjoin', "w'", "t'", "v'"), A('eq', 't', "t'"), A('eq', 'v', "v'")], A('eq', 'w', "w'"),
    doc="the `∷` identification.")

# ===== C. functionality (`pinSteps`, §4.10(i))
def fun_row(name, pred, out, ins, doc):
    # “y' ins… y. pred y ins → pred y' ins → y = y'”
    row('fun', name, [out + "'"] + list(ins) + [out], [A(pred, out, *ins), A(pred, out + "'", *ins)], A('eq', out, out + "'"), doc=doc)
fun_row('qqAndFun', 'qqAnd', 'y', ['p', 'q'], "`y = p ⋏ q → y' = p ⋏ q → y = y'`.")
fun_row('qqOrFun', 'qqOr', 'y', ['p', 'q'], "functionality of `⋎`.")
fun_row('qqAllFun', 'qqAll', 'y', ['p'], "functionality of `∀`.")
fun_row('qqExsFun', 'qqExs', 'y', ['p'], "functionality of `∃`.")
fun_row('qqRelFun', 'qqRel', 'y', ['k', 'R', 'v'], "functionality of `rel`.")
fun_row('qqNRelFun', 'qqNRel', 'y', ['k', 'R', 'v'], "functionality of `nrel`.")
fun_row('qqVerumFun', 'qqVerum', 'y', [], "functionality of `⊤`.")
fun_row('qqFalsumFun', 'qqFalsum', 'y', [], "functionality of `⊥`.")
fun_row('qqFuncFun', 'qqFunc', 'y', ['k', 'f', 'v'], "functionality of `func`.")
fun_row('qqBvarFun', 'qqBvar', 'y', ['z'], "functionality of `#z`.")
fun_row('qqFvarFun', 'qqFvar', 'y', ['x'], "functionality of `&x`.")
fun_row('adjoinFun', 'adjoin', 'y', ['t', 'v'], "functionality of `∷`.")
fun_row('setShiftFun', 'setShiftG', 'y', ['s'], "functionality of `setShift`.")
fun_row('setLenFun', 'setLen', 'y', ['s'], "functionality of `setLen`.")
fun_row('lengthFun', 'length', 'y', ['k'], "functionality of `‖·‖`.")
fun_row('termLenVecFun', 'tlvG', 'y', ['k', 'v'], "functionality of `termLenVec`.")
fun_row('listSumFun', 'listSum', 'y', ['M'], "functionality of `listSum`.")
fun_row('formulaLenFun', 'flenG', 'y', ['p'], "functionality of `formulaLen`.")
fun_row('termLenFun', 'tlenG', 'y', ['t'], "functionality of `termLen`.")
fun_row('fstIdxFun', 'fstIdx', 'y', ['d'], "functionality of `fstIdx`.")
fun_row('insertFun', 'insert', 'y', ['x', 's'], "functionality of `insert`.")
fun_row('negFun', 'negG', 'y', ['p'], "functionality of `neg`.")
fun_row('shiftFun', 'shiftG', 'y', ['p'], "functionality of `shift`.")
fun_row('substsFun', 'substsG', 'y', ['w', 'p'], "functionality of `subst`.")
fun_row('substs1Fun', 'substs1G', 'y', ['t', 'p'], "functionality of `substs1`.")
fun_row('freeFun', 'freeG', 'y', ['p'], "functionality of `free`.")
fun_row('bnumFun', 'bnumG', 'y', ['k'], "functionality of `bnum`.")
fun_row('nthFun', 'nth', 'y', ['w', 'i'], "functionality of `nth`.")
fun_row('fvarVecFun', 'fvarVec', 'y', ['m'], "functionality of `fvarVec`.")
fun_row('termShiftFun', 'tshG', 'y', ['t'], "functionality of `termShift`.")
fun_row('termSubstFun', 'tsG', 'y', ['w', 't'], "functionality of `termSubst`.")
fun_row('termBShiftFun', 'tbshG', 'y', ['t'], "functionality of `termBShift`.")
fun_row('qqAllsFun', 'alls', 'y', ['b', 'm'], "functionality of `qqAlls`.")
fun_row('bvFun', 'bvG', 'y', ['b'], "functionality of `bv`.")
fun_row('qVecFun', 'qVecG', 'y', ['w'], "functionality of `qVec`.")
fun_row('termShiftVecFun', 'tshvG', 'y', ['k', 'v'], "functionality of `termShiftVec`.")
fun_row('termSubstVecFun', 'tsvG', 'y', ['k', 'w', 'v'], "functionality of `termSubstVec`.")

# ===== D. sets (§3.4, §4.5)
row('sets', 'subsetAntisymm', ['t', 's'], [A('subset', 's', 't'), A('subset', 't', 's')], A('eq', 's', 't'),
    'fun _ _ h₁ h₂ ↦ mem_ext fun i ↦ ⟨fun h ↦ h₁ h, fun h ↦ h₂ h⟩',
    "`s ⊆ t → t ⊆ s → s = t` (extensionality of bit-sets, `mem_ext`).")
row('sets', 'setShiftInsert', ["u'", 'u', 'y', 'x', "s'", 's'],
    [A('insert', "s'", 'x', 's'), A('setShiftG', 'u', 's'), A('shiftG', 'y', 'x'), A('insert', "u'", 'y', 'u')], A('setShiftG', "u'", "s'"),
    by('subst_vars; exact (setShift_insert _ _).symm'),
    "`s' = insert x s → u = setShift s → y = shift x → u' = insert y u → u' = setShift s'` (`setShift_insert`).")
row('sets', 'setShiftEmpty', ['u'], [A('setShiftG', 'u', 'Z')], A('eq', 'u', 'Z'),
    by('subst_vars; exact setShift_zero'), "`u = setShift ∅ → u = ∅` (`∅ = 0`).")

# ===== E. the ten `fstIdx<Tag>` rows (§4.0 step 2)
row('fstIdx', 'fstIdxAxL', ['e', 'p', 's'], [A('axL', 'e', 's', 'p')], A('fstIdx', 's', 'e'), by('subst_vars; simp'),
    "`e = axL s p → fstIdx e = s`.")
row('fstIdx', 'fstIdxVerum', ['e', 's'], [A('verumIntro', 'e', 's')], A('fstIdx', 's', 'e'), by('subst_vars; simp'),
    "`e = verumIntro s → fstIdx e = s`.")
row('fstIdx', 'fstIdxAnd', ['e', 'dq', 'dp', 'q', 'p', 's'], [A('andIntro', 'e', 's', 'p', 'q', 'dp', 'dq')], A('fstIdx', 's', 'e'),
    by('subst_vars; simp'), "`e = andIntro s p q dp dq → fstIdx e = s`.")
row('fstIdx', 'fstIdxOr', ['e', 'd', 'q', 'p', 's'], [A('orIntro', 'e', 's', 'p', 'q', 'd')], A('fstIdx', 's', 'e'),
    by('subst_vars; simp'), "`e = orIntro s p q d → fstIdx e = s`.")
row('fstIdx', 'fstIdxAll', ['e', 'd', 'p', 's'], [A('allIntro', 'e', 's', 'p', 'd')], A('fstIdx', 's', 'e'),
    by('subst_vars; simp'), "`e = allIntro s p d → fstIdx e = s`.")
row('fstIdx', 'fstIdxExs', ['e', 'd', 't', 'p', 's'], [A('exsIntro', 'e', 's', 'p', 't', 'd')], A('fstIdx', 's', 'e'),
    by('subst_vars; simp'), "`e = exsIntro s p t d → fstIdx e = s`.")
row('fstIdx', 'fstIdxWk', ['e', 'd', 's'], [A('wkRule', 'e', 's', 'd')], A('fstIdx', 's', 'e'),
    by('subst_vars; simp'), "`e = wkRule s d → fstIdx e = s`.")
row('fstIdx', 'fstIdxShift', ['e', 'd', 's'], [A('shiftRule', 'e', 's', 'd')], A('fstIdx', 's', 'e'),
    by('subst_vars; simp'), "`e = shiftRule s d → fstIdx e = s` (the node's sequent is the shifted one, `introShiftB`).")
row('fstIdx', 'fstIdxCut', ['e', 'd₂', 'd₁', 'p', 's'], [A('cutRule', 'e', 's', 'p', 'd₁', 'd₂')], A('fstIdx', 's', 'e'),
    by('subst_vars; simp'), "`e = cutRule s p d₁ d₂ → fstIdx e = s`.")
row('fstIdx', 'fstIdxAxm', ['e', 'p', 's'], [A('axm', 'e', 's', 'p')], A('fstIdx', 's', 'e'),
    by('subst_vars; simp'), "`e = axm s p → fstIdx e = s`.")

# ===== F. the top's node rows (§7.1)
row('nodes', 'dlenDefIntro', ['n', 'd'], [A('deriv', 'd'), A('dlen', 'd', 'n')], A('dlenDef', 'n', 'd'),
    'fun _ _ h₁ h₂ ↦ (dlen_eq_of_graph h₁ h₂).symm',
    "`derivation d → dlenGraph d n → dlen d = n` (the `dlenDef` graph from the derivation graph, §7.1 step 7).")
row('nodes', 'proofIntro', ['d', 'g', 's'], [A('insert', 's', 'g', 'Z'), A('fstIdx', 's', 'd'), A('deriv', 'd')], A('proof', 'd', 'g'),
    'fun _ _ _ h₁ h₂ h₃ ↦ ⟨by rw [← h₂, h₁]; exact mem_ext fun _ ↦ by simp, h₃⟩',
    "`s = insert g ∅ → fstIdx d = s → derivation d → proof d g`.")
row('nodes', 'instBIntro', ['g', 'v', 't', 'k', 'n'], [A('bnumG', 't', 'k'), A('adjoin', 'v', 't', 'Z'), A('substsG', 'g', 'v', 'n')],
    A('instBG', 'g', 'n', 'k'), doc="`t = bnum k → v = t ∷ 0 → g = subst v n → g = instB n k`.")
row('nodes', 'gIntro', ['a', 'l', 'k'], [A('length', 'l', 'k'), A('eq', 'a', M(M('l', 'l'), 'l'))], A('gG', 'a', 'k'),
    doc="`l = ‖k‖ → a = l * l * l → a = gBudget k`.")
row('nodes', 'lengthTotal', ['k'], [], EX(['l'], [A('length', 'l', 'k')]), 'fun _ ↦ ⟨_, rfl⟩', "`∀ k, ∃ l, l = ‖k‖`.")
row('nodes', 'bnumZeroCert', ['t'], [A('qqFunc', 't', 'Z', 'Z', 'Z')], A('bnumG', 't', 'Z'),
    by('subst_vars; rw [bnum_zero]; simp only [Arithmetic.zero, qqFuncN_eq_qqFunc, qqFunc_absolute, coe_zeroIndex_eq, Nat.cast_zero]'), "`t = func 0 0 0 → t = bnum 0` (`𝟎` as the walk writes it).")
row('nodes', 'bnumOneCert', ['t'], [A('qqFunc', 't', 'Z', C(1), 'Z')], A('bnumG', 't', 'One'),
    by('subst_vars; rw [bnum_one]; simp only [Arithmetic.one, qqFuncN_eq_qqFunc, qqFunc_absolute, coe_oneIndex_eq, Nat.cast_zero, zero_add]'), "`t = func 0 (0 + 1) 0 → t = bnum 1` (`𝟏` as the walk writes it).")
row('nodes', 'bnumEvenCert', ['u', 'v', "v'", 'two', 'w', "w'", 'one', 't', 'm'],
    [A('le', 'One', 'm'), A('bnumG', 't', 'm'), A('qqFunc', 'one', 'Z', C(1), 'Z'), A('adjoin', "w'", 'one', 'Z'),
     A('adjoin', 'w', 'one', "w'"), A('qqFunc', 'two', C(2), 'Z', 'w'), A('adjoin', "v'", 't', 'Z'), A('adjoin', 'v', 'two', "v'"),
     A('qqFunc', 'u', C(2), C(1), 'v')], A('bnumG', 'u', M('Two', 'm')),
    by('subst_vars; rw [bnum_two_mul h₁]; simp only [qqTwo, qqMul, qqAdd, coe_mulIndex_eq, coe_addIndex_eq, Arithmetic.one, qqFuncN_eq_qqFunc, qqFunc_absolute, coe_oneIndex_eq, Nat.cast_zero, zero_add, one_add_one_eq_two]'),
    "`1 ≤ m → t = bnum m → u = 𝟐 ^* t (as `func`/`∷` facts) → u = bnum (2 * m)` (`bnum_two_mul`).")
row('nodes', 'bnumOddCert', ['u', 'x', "x'", 's', 'v', "v'", 'two', 'w', "w'", 'one', 't', 'm'],
    [A('le', 'One', 'm'), A('bnumG', 't', 'm'), A('qqFunc', 'one', 'Z', C(1), 'Z'), A('adjoin', "w'", 'one', 'Z'),
     A('adjoin', 'w', 'one', "w'"), A('qqFunc', 'two', C(2), 'Z', 'w'), A('adjoin', "v'", 't', 'Z'), A('adjoin', 'v', 'two', "v'"),
     A('qqFunc', 's', C(2), C(1), 'v'), A('adjoin', "x'", 'one', 'Z'), A('adjoin', 'x', 's', "x'"), A('qqFunc', 'u', C(2), 'Z', 'x')],
    A('bnumG', 'u', P(M('Two', 'm'), 'One')),
    by('subst_vars; rw [bnum_two_mul_add_one h₁]; simp only [qqTwo, qqMul, qqAdd, coe_mulIndex_eq, coe_addIndex_eq, Arithmetic.one, qqFuncN_eq_qqFunc, qqFunc_absolute, coe_oneIndex_eq, Nat.cast_zero, zero_add, one_add_one_eq_two]'),
    "`1 ≤ m → t = bnum m → u = (𝟐 ^* t) ^+ 𝟏 (as `func`/`∷` facts) → u = bnum (2 * m + 1)` (`bnum_two_mul_add_one`).")

# ===== G. lengths (§3.6)
row('lengths', 'termLenVecNil', ['x'], [], A('tlvG', 'Z', 'Z', 'Z'), 'fun _ ↦ by exact termLenVec_nil.symm', "`termLenVec 0 0 = 0` (dummy binder `x`: a CLOSED row over a blueprint graph hangs `simp`).")
row('lengths', 'termLenVecAdj', ["M'", 'M', 'l', 't', "v'", 'v', 'k', 'n'],
    [A('tpi', 'n', 't'), A('utvpi', 'k', 'v'), A('tlenG', 'l', 't'), A('tlvG', 'M', 'k', 'v'), A('adjoin', "v'", 't', 'v'), A('adjoin', "M'", 'l', 'M')],
    A('tlvG', "M'", S('k'), "v'"), by('subst_vars; exact (termLenVec_cons h₁.isUTerm h₂).symm'),
    "`termLenVec (k + 1) (t ∷ v) = termLen t ∷ termLenVec k v` bottom-up.")
row('lengths', 'listSumNil', ['x'], [], A('listSum', 'Z', 'Z'), 'fun _ ↦ by exact listSum_nil.symm', "`listSum 0 = 0` (dummy binder).")
row('lengths', 'listSumAdj', ["s'", 's', 'l', 'M', "M'"], [A('listSum', 's', 'M'), A('adjoin', "M'", 'l', 'M'), A('listSum', "s'", "M'")],
    A('eq', "s'", P('l', 's')), by('subst_vars; exact listSum_adjoin _ _'), "`listSum (l ∷ M) = l + listSum M`.")
row('lengths', 'formulaLenRelCert', ['l', 's', 'M', 'p', 'v', 'R', 'k'],
    [A('isRel', 'k', 'R'), A('utvpi', 'k', 'v'), A('qqRel', 'p', 'k', 'R', 'v'), A('tlvG', 'M', 'k', 'v'), A('listSum', 's', 'M'), A('flenG', 'l', 'p')],
    A('eq', 'l', S('s')), by('subst_vars; exact formulaLen_rel h₁ h₂'),
    "`formulaLen (rel k R v) = listSum (termLenVec k v) + 1` with `M, s` universal (§3.6).")
row('lengths', 'formulaLenNRelCert', ['l', 's', 'M', 'p', 'v', 'R', 'k'],
    [A('isRel', 'k', 'R'), A('utvpi', 'k', 'v'), A('qqNRel', 'p', 'k', 'R', 'v'), A('tlvG', 'M', 'k', 'v'), A('listSum', 's', 'M'), A('flenG', 'l', 'p')],
    A('eq', 'l', S('s')), by('subst_vars; exact formulaLen_nrel h₁ h₂'), "the `nrel` twin.")
row('lengths', 'termLenFuncCert', ['l', 's', 'M', 't', 'v', 'f', 'k'],
    [A('isFunc', 'k', 'f'), A('utvpi', 'k', 'v'), A('qqFunc', 't', 'k', 'f', 'v'), A('tlvG', 'M', 'k', 'v'), A('listSum', 's', 'M'), A('tlenG', 'l', 't')],
    A('eq', 'l', S('s')), by('subst_vars; exact termLen_func h₁ h₂'),
    "`termLen (func k f v) = listSum (termLenVec k v) + 1` with `M, s` universal.")

# ===== H. certification (bottom-up re-description, §3.6)
row('cert', 'negRelCert', ['y', 'v', 'R', 'k', 'r'],
    [A('isRel', 'k', 'R'), A('utvpi', 'k', 'v'), A('qqRel', 'r', 'k', 'R', 'v'), A('qqNRel', 'y', 'k', 'R', 'v')], A('negG', 'y', 'r'),
    by('subst_vars; exact (neg_rel h₁ h₂).symm'), "`neg (rel k R v) = nrel k R v` bottom-up.")
row('cert', 'negNRelCert', ['y', 'v', 'R', 'k', 'r'],
    [A('isRel', 'k', 'R'), A('utvpi', 'k', 'v'), A('qqNRel', 'r', 'k', 'R', 'v'), A('qqRel', 'y', 'k', 'R', 'v')], A('negG', 'y', 'r'),
    by('subst_vars; exact (neg_nrel h₁ h₂).symm'), "`neg (nrel k R v) = rel k R v` bottom-up.")
row('cert', 'negVerumCert', ['y', 'r'], [A('qqVerum', 'r'), A('qqFalsum', 'y')], A('negG', 'y', 'r'),
    by('subst_vars; exact neg_verum.symm'), "`neg ⊤ = ⊥`.")
row('cert', 'negFalsumCert', ['y', 'r'], [A('qqFalsum', 'r'), A('qqVerum', 'y')], A('negG', 'y', 'r'),
    by('subst_vars; exact neg_falsum.symm'), "`neg ⊥ = ⊤`.")
row('cert', 'negAndCert', ['y', 'nq', 'np', 'r', 'q', 'p', 'n'],
    [A('pi', 'n', 'p'), A('pi', 'n', 'q'), A('qqAnd', 'r', 'p', 'q'), A('negG', 'np', 'p'), A('negG', 'nq', 'q'), A('qqOr', 'y', 'np', 'nq')],
    A('negG', 'y', 'r'), by('subst_vars; exact (neg_and h₁.isUFormula h₂.isUFormula).symm'), "`neg (p ⋏ q) = neg p ⋎ neg q` bottom-up.")
row('cert', 'negOrCert', ['y', 'nq', 'np', 'r', 'q', 'p', 'n'],
    [A('pi', 'n', 'p'), A('pi', 'n', 'q'), A('qqOr', 'r', 'p', 'q'), A('negG', 'np', 'p'), A('negG', 'nq', 'q'), A('qqAnd', 'y', 'np', 'nq')],
    A('negG', 'y', 'r'), by('subst_vars; exact (neg_or h₁.isUFormula h₂.isUFormula).symm'), "`neg (p ⋎ q) = neg p ⋏ neg q` bottom-up.")
row('cert', 'negAllCert', ['y', 'np', 'r', 'p', 'n'],
    [A('pi', S('n'), 'p'), A('qqAll', 'r', 'p'), A('negG', 'np', 'p'), A('qqExs', 'y', 'np')], A('negG', 'y', 'r'),
    by('subst_vars; exact (neg_all h₁.isUFormula).symm'), "`neg (∀ p) = ∃ neg p` bottom-up.")
row('cert', 'negExsCert', ['y', 'np', 'r', 'p', 'n'],
    [A('pi', S('n'), 'p'), A('qqExs', 'r', 'p'), A('negG', 'np', 'p'), A('qqAll', 'y', 'np')], A('negG', 'y', 'r'),
    by('subst_vars; exact (neg_ex h₁.isUFormula).symm'), "`neg (∃ p) = ∀ neg p` bottom-up.")
row('cert', 'shiftRelCert', ['y', 'u', 'v', 'R', 'k', 'r'],
    [A('isRel', 'k', 'R'), A('utvpi', 'k', 'v'), A('qqRel', 'r', 'k', 'R', 'v'), A('tshvG', 'u', 'k', 'v'), A('qqRel', 'y', 'k', 'R', 'u')],
    A('shiftG', 'y', 'r'), by('subst_vars; exact (shift_rel h₁ h₂).symm'), "`shift (rel k R v) = rel k R (termShiftVec k v)` bottom-up.")
row('cert', 'shiftNRelCert', ['y', 'u', 'v', 'R', 'k', 'r'],
    [A('isRel', 'k', 'R'), A('utvpi', 'k', 'v'), A('qqNRel', 'r', 'k', 'R', 'v'), A('tshvG', 'u', 'k', 'v'), A('qqNRel', 'y', 'k', 'R', 'u')],
    A('shiftG', 'y', 'r'), by('subst_vars; exact (shift_nrel h₁ h₂).symm'), "the `nrel` twin.")
row('cert', 'shiftVerumCert', ['y', 'r'], [A('qqVerum', 'r'), A('qqVerum', 'y')], A('shiftG', 'y', 'r'),
    by('subst_vars; exact shift_verum.symm'), "`shift ⊤ = ⊤`.")
row('cert', 'shiftFalsumCert', ['y', 'r'], [A('qqFalsum', 'r'), A('qqFalsum', 'y')], A('shiftG', 'y', 'r'),
    by('subst_vars; exact shift_falsum.symm'), "`shift ⊥ = ⊥`.")
row('cert', 'shiftAndCert', ['y', 'sq', 'sp', 'r', 'q', 'p', 'n'],
    [A('pi', 'n', 'p'), A('pi', 'n', 'q'), A('qqAnd', 'r', 'p', 'q'), A('shiftG', 'sp', 'p'), A('shiftG', 'sq', 'q'), A('qqAnd', 'y', 'sp', 'sq')],
    A('shiftG', 'y', 'r'), by('subst_vars; exact (shift_and h₁.isUFormula h₂.isUFormula).symm'), "`shift (p ⋏ q)` bottom-up.")
row('cert', 'shiftOrCert', ['y', 'sq', 'sp', 'r', 'q', 'p', 'n'],
    [A('pi', 'n', 'p'), A('pi', 'n', 'q'), A('qqOr', 'r', 'p', 'q'), A('shiftG', 'sp', 'p'), A('shiftG', 'sq', 'q'), A('qqOr', 'y', 'sp', 'sq')],
    A('shiftG', 'y', 'r'), by('subst_vars; exact (shift_or h₁.isUFormula h₂.isUFormula).symm'), "`shift (p ⋎ q)` bottom-up.")
row('cert', 'shiftAllCert', ['y', 'sp', 'r', 'p', 'n'],
    [A('pi', S('n'), 'p'), A('qqAll', 'r', 'p'), A('shiftG', 'sp', 'p'), A('qqAll', 'y', 'sp')], A('shiftG', 'y', 'r'),
    by('subst_vars; exact (shift_all h₁.isUFormula).symm'), "`shift (∀ p)` bottom-up.")
row('cert', 'shiftExsCert', ['y', 'sp', 'r', 'p', 'n'],
    [A('pi', S('n'), 'p'), A('qqExs', 'r', 'p'), A('shiftG', 'sp', 'p'), A('qqExs', 'y', 'sp')], A('shiftG', 'y', 'r'),
    by('subst_vars; exact (shift_exs h₁.isUFormula).symm'), "`shift (∃ p)` bottom-up.")
row('cert', 'substsRelCert', ['y', 'u', 'v', 'R', 'k', 'r', 'w'],
    [A('isRel', 'k', 'R'), A('utvpi', 'k', 'v'), A('qqRel', 'r', 'k', 'R', 'v'), A('tsvG', 'u', 'k', 'w', 'v'), A('qqRel', 'y', 'k', 'R', 'u')],
    A('substsG', 'y', 'w', 'r'), by('subst_vars; exact (substs_rel h₁ h₂).symm'), "`subst w (rel k R v) = rel k R (termSubstVec k w v)` bottom-up.")
row('cert', 'substsNRelCert', ['y', 'u', 'v', 'R', 'k', 'r', 'w'],
    [A('isRel', 'k', 'R'), A('utvpi', 'k', 'v'), A('qqNRel', 'r', 'k', 'R', 'v'), A('tsvG', 'u', 'k', 'w', 'v'), A('qqNRel', 'y', 'k', 'R', 'u')],
    A('substsG', 'y', 'w', 'r'), by('subst_vars; exact (substs_nrel h₁ h₂).symm'), "the `nrel` twin.")
row('cert', 'substsVerumCert', ['y', 'r', 'w'], [A('qqVerum', 'r'), A('qqVerum', 'y')], A('substsG', 'y', 'w', 'r'),
    by('subst_vars; exact (substs_verum _).symm'), "`subst w ⊤ = ⊤`.")
row('cert', 'substsFalsumCert', ['y', 'r', 'w'], [A('qqFalsum', 'r'), A('qqFalsum', 'y')], A('substsG', 'y', 'w', 'r'),
    by('subst_vars; exact (substs_falsum _).symm'), "`subst w ⊥ = ⊥`.")
row('cert', 'substsAndCert', ['y', 'sq', 'sp', 'r', 'q', 'p', 'n', 'w'],
    [A('pi', 'n', 'p'), A('pi', 'n', 'q'), A('qqAnd', 'r', 'p', 'q'), A('substsG', 'sp', 'w', 'p'), A('substsG', 'sq', 'w', 'q'), A('qqAnd', 'y', 'sp', 'sq')],
    A('substsG', 'y', 'w', 'r'), by('subst_vars; exact (substs_and h₁.isUFormula h₂.isUFormula).symm'), "`subst w (p ⋏ q)` bottom-up.")
row('cert', 'substsOrCert', ['y', 'sq', 'sp', 'r', 'q', 'p', 'n', 'w'],
    [A('pi', 'n', 'p'), A('pi', 'n', 'q'), A('qqOr', 'r', 'p', 'q'), A('substsG', 'sp', 'w', 'p'), A('substsG', 'sq', 'w', 'q'), A('qqOr', 'y', 'sp', 'sq')],
    A('substsG', 'y', 'w', 'r'), by('subst_vars; exact (substs_or h₁.isUFormula h₂.isUFormula).symm'), "`subst w (p ⋎ q)` bottom-up.")
row('cert', 'substsAllCert', ['y', 'sp', 'u', 'r', 'p', 'n', 'w'],
    [A('pi', S('n'), 'p'), A('qqAll', 'r', 'p'), A('qVecG', 'u', 'w'), A('substsG', 'sp', 'u', 'p'), A('qqAll', 'y', 'sp')],
    A('substsG', 'y', 'w', 'r'), by('subst_vars; exact (substs_all h₁.isUFormula).symm'), "`subst w (∀ p) = ∀ subst (qVec w) p` bottom-up.")
row('cert', 'substsExsCert', ['y', 'sp', 'u', 'r', 'p', 'n', 'w'],
    [A('pi', S('n'), 'p'), A('qqExs', 'r', 'p'), A('qVecG', 'u', 'w'), A('substsG', 'sp', 'u', 'p'), A('qqExs', 'y', 'sp')],
    A('substsG', 'y', 'w', 'r'), by('subst_vars; exact (substs_ex h₁.isUFormula).symm'), "`subst w (∃ p) = ∃ subst (qVec w) p` bottom-up.")
row('cert', 'freeCert', ['fp', 'sp', 'z', 'p'], [A('qqFvar', 'z', 'Z'), A('shiftG', 'sp', 'p'), A('substs1G', 'fp', 'z', 'sp')], A('freeG', 'fp', 'p'),
    doc="`z = &0 → sp = shift p → fp = substs1 z sp → fp = free p` (Foundation's definition of `free`).")
row('cert', 'substsSubsts1', ['y', 'w', 't', 'p'], [A('adjoin', 'w', 't', 'Z'), A('substsG', 'y', 'w', 'p')], A('substs1G', 'y', 't', 'p'),
    doc="`w = t ∷ 0 → y = subst w p → y = substs1 t p` (the converse of `substs1Substs`).")
# term level: shift
row('cert', 'tshvNilCert', ['x'], [], A('tshvG', 'Z', 'Z', 'Z'), 'fun _ ↦ by exact termShiftVec_nil.symm', "`termShiftVec 0 0 = 0` (dummy binder).")
row('cert', 'tshvAdjCert', ["u'", 'u', "t'", 't', "v'", 'v', 'k', 'n'],
    [A('tpi', 'n', 't'), A('utvpi', 'k', 'v'), A('tshG', "t'", 't'), A('tshvG', 'u', 'k', 'v'), A('adjoin', "v'", 't', 'v'), A('adjoin', "u'", "t'", 'u')],
    A('tshvG', "u'", S('k'), "v'"), by('subst_vars; exact (termShiftVec_cons h₁.isUTerm h₂).symm'),
    "`termShiftVec (k + 1) (t ∷ v) = termShift t ∷ termShiftVec k v` bottom-up.")
row('cert', 'termShiftBvarCert', ["t'", 't', 'z'], [A('qqBvar', 't', 'z'), A('qqBvar', "t'", 'z')], A('tshG', "t'", 't'),
    by('subst_vars; exact (termShift_bvar _).symm'), "`termShift #z = #z`.")
row('cert', 'termShiftFvarCert', ["t'", 't', 'x'], [A('qqFvar', 't', 'x'), A('qqFvar', "t'", S('x'))], A('tshG', "t'", 't'),
    by('subst_vars; exact (termShift_fvar _).symm'), "`termShift &x = &(x + 1)`.")
row('cert', 'termShiftFuncCert', ["t'", 'u', 'v', 'f', 'k', 't'],
    [A('isFunc', 'k', 'f'), A('utvpi', 'k', 'v'), A('qqFunc', 't', 'k', 'f', 'v'), A('tshvG', 'u', 'k', 'v'), A('qqFunc', "t'", 'k', 'f', 'u')],
    A('tshG', "t'", 't'), by('subst_vars; exact (termShift_func h₁ h₂).symm'), "`termShift (func k f v) = func k f (termShiftVec k v)`.")
# term level: subst
row('cert', 'tsvNilCert', ['w'], [], A('tsvG', 'Z', 'Z', 'w', 'Z'), 'fun _ ↦ by exact (termSubstVec_nil _).symm', "`termSubstVec 0 w 0 = 0`.")
row('cert', 'tsvAdjCert', ["u'", 'u', 'e', 't', "v'", 'v', 'w', 'k', 'n'],
    [A('tpi', 'n', 't'), A('utvpi', 'k', 'v'), A('tsG', 'e', 'w', 't'), A('tsvG', 'u', 'k', 'w', 'v'), A('adjoin', "v'", 't', 'v'), A('adjoin', "u'", 'e', 'u')],
    A('tsvG', "u'", S('k'), 'w', "v'"), by('subst_vars; exact (termSubstVec_cons h₁.isUTerm h₂).symm'),
    "`termSubstVec (k + 1) w (t ∷ v) = termSubst w t ∷ termSubstVec k w v` bottom-up.")
row('cert', 'termSubstBvarCert', ['e', 'w', 'z', 't'], [A('qqBvar', 't', 'z'), A('nth', 'e', 'w', 'z')], A('tsG', 'e', 'w', 't'),
    by('subst_vars; exact (termSubst_bvar _).symm'), "`termSubst w #z = w.[z]`.")
row('cert', 'termSubstFvarCert', ['e', 'w', 'x', 't'], [A('qqFvar', 't', 'x'), A('qqFvar', 'e', 'x')], A('tsG', 'e', 'w', 't'),
    by('subst_vars; exact (termSubst_fvar _).symm'), "`termSubst w &x = &x`.")
row('cert', 'termSubstFuncCert', ['e', 'u', 'v', 'f', 'k', 't', 'w'],
    [A('isFunc', 'k', 'f'), A('utvpi', 'k', 'v'), A('qqFunc', 't', 'k', 'f', 'v'), A('tsvG', 'u', 'k', 'w', 'v'), A('qqFunc', 'e', 'k', 'f', 'u')],
    A('tsG', 'e', 'w', 't'), by('subst_vars; exact (termSubst_func h₁ h₂).symm'), "`termSubst w (func k f v) = func k f (termSubstVec k w v)`.")
# term level: bShift and qVec
row('cert', 'tbshvNilCert', ['x'], [], A('tbshvG', 'Z', 'Z', 'Z'), 'fun _ ↦ by exact termBShiftVec_nil.symm', "`termBShiftVec 0 0 = 0` (dummy binder).")
row('cert', 'tbshvAdjCert', ["u'", 'u', "t'", 't', "v'", 'v', 'k', 'n'],
    [A('tpi', 'n', 't'), A('utvpi', 'k', 'v'), A('tbshG', "t'", 't'), A('tbshvG', 'u', 'k', 'v'), A('adjoin', "v'", 't', 'v'), A('adjoin', "u'", "t'", 'u')],
    A('tbshvG', "u'", S('k'), "v'"), by('subst_vars; exact (termBShiftVec_cons h₁.isUTerm h₂).symm'),
    "`termBShiftVec (k + 1) (t ∷ v) = termBShift t ∷ termBShiftVec k v` bottom-up.")
row('cert', 'termBShiftBvarCert', ["t'", 't', 'z'], [A('qqBvar', 't', 'z'), A('qqBvar', "t'", S('z'))], A('tbshG', "t'", 't'),
    by('subst_vars; exact (termBShift_bvar _).symm'), "`termBShift #z = #(z + 1)`.")
row('cert', 'termBShiftFvarCert', ["t'", 't', 'x'], [A('qqFvar', 't', 'x'), A('qqFvar', "t'", 'x')], A('tbshG', "t'", 't'),
    by('subst_vars; exact (termBShift_fvar _).symm'), "`termBShift &x = &x`.")
row('cert', 'termBShiftFuncCert', ["t'", 'u', 'v', 'f', 'k', 't'],
    [A('isFunc', 'k', 'f'), A('utvpi', 'k', 'v'), A('qqFunc', 't', 'k', 'f', 'v'), A('tbshvG', 'u', 'k', 'v'), A('qqFunc', "t'", 'k', 'f', 'u')],
    A('tbshG', "t'", 't'), by('subst_vars; exact (termBShift_func h₁ h₂).symm'), "`termBShift (func k f v) = func k f (termBShiftVec k v)`.")
row('cert', 'qVecCert', ['u', 'sw', 'z', 'w', 'k'],
    [A('utvpi', 'k', 'w'), A('tbshvG', 'sw', 'k', 'w'), A('qqBvar', 'z', 'Z'), A('adjoin', 'u', 'z', 'sw')], A('qVecG', 'u', 'w'),
    by('subst_vars; unfold qVec; rw [h₁.lh]'), "`qVec w = #0 ∷ termBShiftVec (len w) w` bottom-up (`len w = k` from `IsUTermVec k w`).")
row('cert', 'qVecNth0', ['u', 'w'], [A('qVecG', 'u', 'w')], EX(['z'], [A('qqBvar', 'z', 'Z'), A('nth', 'z', 'u', 'Z')]),
    'fun _ _ h ↦ ⟨_, rfl, by subst h; simp [qVec]⟩', "`(qVec w).[0] = #0`.")
row('cert', 'qVecNthSucc', ["e'", 'e', 'u', 'w', 'i', 'k'],
    [A('utvpi', 'k', 'w'), A('lt', 'i', 'k'), A('qVecG', 'u', 'w'), A('nth', 'e', 'w', 'i'), A('tbshG', "e'", 'e')], A('nth', "e'", 'u', S('i')),
    by('subst_vars; unfold qVec; rw [nth_adjoin_succ, ← h₁.lh, nth_termBShiftVec h₁ h₂]'),
    "`i < k → (qVec w).[i + 1] = termBShift w.[i]` for a `k`-vector `w`.")
row('cert', 'nthAdjoinZero', ['w', 't', 'v'], [A('adjoin', 'w', 't', 'v')], A('nth', 't', 'w', 'Z'), by('subst_vars; simp'),
    "`(t ∷ v).[0] = t`.")
row('cert', 'nthAdjoinSucc', ['e', 'w', 't', 'v', 'i'], [A('adjoin', 'w', 't', 'v'), A('nth', 'e', 'v', 'i')], A('nth', 'e', 'w', S('i')),
    by('subst_vars; simp'), "`(t ∷ v).[i + 1] = v.[i]`.")

# ===== I. numerals (N4/N5, §2.4), in the DSL
row('num', 'twoMulMul', ['y', 'x'], [], A('eq', M('x', M('Two', 'y')), M('Two', M('x', 'y'))), 'fun _ _ ↦ mul_left_comm _ _ _',
    "`x * (2 * y) = 2 * (x * y)` (N4, the even bit).")
row('num', 'twoMulOneMul', ['y', 'x'], [], A('eq', M('x', P(M('Two', 'y'), 'One')), P(M('Two', M('x', 'y')), 'x')),
    'fun _ _ ↦ by rw [mul_add, mul_one, mul_left_comm]', "`x * (2 * y + 1) = 2 * (x * y) + x` (N4, the odd bit).")
row('num', 'lengthZero', ['x'], [], A('length', 'Z', 'Z'), 'fun _ ↦ length_zero.symm', "`‖0‖ = 0` (N5; dummy binder).")
row('num', 'lengthOne', ['x'], [], A('length', 'One', 'One'), 'fun _ ↦ length_one.symm', "`‖1‖ = 1` (N5; dummy binder).")
row('num', 'lengthTwoMul', ['l', 'x'], [A('lt', 'Z', 'x'), A('length', 'l', 'x')], A('length', S('l'), M('Two', 'x')),
    by('subst_vars; exact (length_two_mul_of_pos h₁).symm'), "`0 < x → ‖2x‖ = ‖x‖ + 1` (N5).")
row('num', 'lengthTwoMulOne', ['l', 'x'], [A('length', 'l', 'x')], A('length', S('l'), P(M('Two', 'x'), 'One')),
    by('subst_vars; exact (length_two_mul_add_one _).symm'), "`‖2x + 1‖ = ‖x‖ + 1` (N5).")

# ===== J. `axm`(ii): the induction-instance recognizer's shape rows (§4.10(ii))
row('axm', 'qqAllsZero', ['b'], [], A('alls', 'b', 'b', 'Z'), 'fun _ ↦ (qqAlls_zero _).symm', "`qqAlls b 0 = b`.")
row('axm', 'qqAllsSucc', ["p'", 'p', 'b', 'm'], [A('alls', 'p', 'b', 'm'), A('qqAll', "p'", 'p')], A('alls', "p'", 'b', S('m')),
    by('subst_vars; exact (qqAlls_succ _ _).symm'), "`qqAlls b (m + 1) = ∀ (qqAlls b m)`.")
row('axm', 'bvRel', ['m', 'M', 'v', 'R', 'k', 'p'],
    [A('isRel', 'k', 'R'), A('utvpi', 'k', 'v'), A('qqRel', 'p', 'k', 'R', 'v'), A('termBVVecG', 'M', 'k', 'v'), A('listMax', 'm', 'M')],
    A('bvG', 'm', 'p'), by('subst_vars; exact (bv_rel h₁ h₂).symm'), "`bv (rel k R v) = listMax (termBVVec k v)`.")
row('axm', 'bvNRel', ['m', 'M', 'v', 'R', 'k', 'p'],
    [A('isRel', 'k', 'R'), A('utvpi', 'k', 'v'), A('qqNRel', 'p', 'k', 'R', 'v'), A('termBVVecG', 'M', 'k', 'v'), A('listMax', 'm', 'M')],
    A('bvG', 'm', 'p'), by('subst_vars; exact (bv_nrel h₁ h₂).symm'), "`bv (nrel k R v) = listMax (termBVVec k v)`.")
row('axm', 'bvVerum', ['p'], [A('qqVerum', 'p')], A('bvG', 'Z', 'p'), by('subst_vars; exact bv_verum.symm'), "`bv ⊤ = 0`.")
row('axm', 'bvFalsum', ['p'], [A('qqFalsum', 'p')], A('bvG', 'Z', 'p'), by('subst_vars; exact bv_falsum.symm'), "`bv ⊥ = 0`.")
row('axm', 'bvAnd', ['m', 'mq', 'mp', 'r', 'q', 'p'],
    [A('ufPi', 'p'), A('ufPi', 'q'), A('qqAnd', 'r', 'p', 'q'), A('bvG', 'mp', 'p'), A('bvG', 'mq', 'q'), A('maxG', 'm', 'mp', 'mq')],
    A('bvG', 'm', 'r'), by('subst_vars; exact (bv_and h₁ h₂).symm'), "`bv (p ⋏ q) = max (bv p) (bv q)`.")
row('axm', 'bvOr', ['m', 'mq', 'mp', 'r', 'q', 'p'],
    [A('ufPi', 'p'), A('ufPi', 'q'), A('qqOr', 'r', 'p', 'q'), A('bvG', 'mp', 'p'), A('bvG', 'mq', 'q'), A('maxG', 'm', 'mp', 'mq')],
    A('bvG', 'm', 'r'), by('subst_vars; exact (bv_or h₁ h₂).symm'), "`bv (p ⋎ q) = max (bv p) (bv q)`.")
row('axm', 'bvAll', ['m', 'mp', 'r', 'p'], [A('ufPi', 'p'), A('qqAll', 'r', 'p'), A('bvG', 'mp', 'p'), A('subG', 'm', 'mp', 'One')],
    A('bvG', 'm', 'r'), by('subst_vars; exact (bv_all h₁).symm'), "`bv (∀ p) = bv p - 1`.")
row('axm', 'bvExs', ['m', 'mp', 'r', 'p'], [A('ufPi', 'p'), A('qqExs', 'r', 'p'), A('bvG', 'mp', 'p'), A('subG', 'm', 'mp', 'One')],
    A('bvG', 'm', 'r'), by('subst_vars; exact (bv_ex h₁).symm'), "`bv (∃ p) = bv p - 1`.")
row('axm', 'termBVBvar', ['t', 'z'], [A('qqBvar', 't', 'z')], A('termBVG', S('z'), 't'), by('subst_vars; exact (termBV_bvar _).symm'),
    "`termBV #z = z + 1`.")
row('axm', 'termBVFvar', ['t', 'x'], [A('qqFvar', 't', 'x')], A('termBVG', 'Z', 't'), by('subst_vars; exact (termBV_fvar _).symm'),
    "`termBV &x = 0`.")
row('axm', 'termBVFunc', ['m', 'M', 'v', 'f', 'k', 't'],
    [A('isFunc', 'k', 'f'), A('utvpi', 'k', 'v'), A('qqFunc', 't', 'k', 'f', 'v'), A('termBVVecG', 'M', 'k', 'v'), A('listMax', 'm', 'M')],
    A('termBVG', 'm', 't'), by('subst_vars; exact (termBV_func h₁ h₂).symm'), "`termBV (func k f v) = listMax (termBVVec k v)`.")
# `termBVVec_nil` is stated at `V : Type` only (`Eq.{1}`): go through the polymorphic `resultVec_nil`
row('axm', 'termBVVecNil', ['x'], [], A('termBVVecG', 'Z', 'Z', 'Z'), 'fun _ ↦ by unfold termBVVec; exact (IsUTerm.BV.construction.resultVec_nil LAct ![]).symm', "`termBVVec 0 0 = 0` (dummy binder).")
row('axm', 'termBVVecAdj', ["M'", 'M', 'm', 't', "v'", 'v', 'k', 'n'],
    [A('tpi', 'n', 't'), A('utvpi', 'k', 'v'), A('termBVG', 'm', 't'), A('termBVVecG', 'M', 'k', 'v'), A('adjoin', "v'", 't', 'v'), A('adjoin', "M'", 'm', 'M')],
    A('termBVVecG', "M'", S('k'), "v'"), by('subst_vars; exact (termBVVec_cons h₁.isUTerm h₂).symm'),
    "`termBVVec (k + 1) (t ∷ v) = termBV t ∷ termBVVec k v` bottom-up.")
row('axm', 'listMaxNil', ['x'], [], A('listMax', 'Z', 'Z'), 'fun _ ↦ by exact listMax_nil.symm', "`listMax 0 = 0` (dummy binder).")
row('axm', 'listMaxAdj', ["m'", 'm', 'x', 'M', "M'"], [A('listMax', 'm', 'M'), A('adjoin', "M'", 'x', 'M'), A('maxG', "m'", 'x', 'm')],
    A('listMax', "m'", "M'"), by('subst_vars; exact (listMax_adjoin _ _).symm'), "`listMax (x ∷ M) = max x (listMax M)`.")
row('axm', 'bvTotal', ['b'], [], EX(['m'], [A('bvG', 'm', 'b')]), 'fun _ ↦ ⟨_, rfl⟩', "`∀ b, ∃ m, m = bv b`.")
row('axm', 'fvarVecTotal', ['m'], [], EX(['fv'], [A('fvarVec', 'fv', 'm')]), 'fun _ ↦ ⟨_, rfl⟩', "`∀ m, ∃ fv, fv = fvarVec m`.")
row('axm', 'fvarVecNth', ['e', 'fv', 'm', 'i'], [A('lt', 'i', 'm'), A('fvarVec', 'fv', 'm'), A('qqFvar', 'e', 'i')], A('nth', 'e', 'fv', 'i'),
    by('subst_vars; exact (nth_fvarVec _ _ h₁).symm'), "`i < m → (fvarVec m).[i] = &i`.")
row('axm', 'maxTotal', ['b', 'a'], [], EX(['m'], [A('maxG', 'm', 'a', 'b')]), 'fun _ _ ↦ ⟨_, rfl⟩', "`∀ a b, ∃ m, m = max a b`.")
row('axm', 'subTotal', ['b', 'a'], [], EX(['m'], [A('subG', 'm', 'a', 'b')]), 'fun _ _ ↦ ⟨_, rfl⟩', "`∀ a b, ∃ m, m = a - b`.")
row('axm', 'maxEqLeft', ['m', 'b', 'a'], [A('le', 'b', 'a'), A('maxG', 'm', 'a', 'b')], A('eq', 'm', 'a'),
    by('subst_vars; exact max_eq_left h₁'), "`b ≤ a → max a b = a`.")
row('axm', 'maxEqRight', ['m', 'b', 'a'], [A('le', 'a', 'b'), A('maxG', 'm', 'a', 'b')], A('eq', 'm', 'b'),
    by('subst_vars; exact max_eq_right h₁'), "`a ≤ b → max a b = b`.")
row('axm', 'subAddCancel', ['m', 'c', 'b', 'a'], [A('eq', 'a', P('b', 'c')), A('subG', 'm', 'a', 'b')], A('eq', 'm', 'c'),
    by('subst_vars; exact add_sub_self\''), "`a = b + c → a - b = c`.")
row('axm', 'subOfLe', ['m', 'b', 'a'], [A('le', 'a', 'b'), A('subG', 'm', 'a', 'b')], A('eq', 'm', 'Z'),
    by('subst_vars; exact sub_spec_of_le h₁'), "`a ≤ b → a - b = 0`.")

GROUPS = None   # {group: (start, end) | None}
if len(sys.argv) > 3:
    GROUPS = {}
    for g in sys.argv[3].split(','):
        if '@' in g:
            name, rng = g.split('@')
            a, b = rng.split('-')
            GROUPS[name] = (int(a), int(b))
        else:
            GROUPS[g] = None

def selected():
    if GROUPS is None:
        return list(ROWS)
    out_rows = []
    counters = {}
    for r in ROWS:
        g = r[0]
        if g not in GROUPS:
            continue
        i = counters.get(g, 0); counters[g] = i + 1
        rng = GROUPS[g]
        if rng is None or rng[0] <= i < rng[1]:
            out_rows.append(r)
    return out_rows

# ----------------------------------------------------------------------------- entry rendering
def dsl(e):
    if isinstance(e, tuple):
        if e[0] == 'S': return f'({dsl(e[1])} + 1)'
        if e[0] == 'C': return '(' + ' + '.join(['0'] + ['1'] * e[1]) + ')' if e[1] > 0 else '0'
        if e[0] == 'P': return f'({dsl(e[1])} + {dsl(e[2])})'
        if e[0] == 'M': return f'({dsl(e[1])} * {dsl(e[2])})'
    return {'Z': '0', 'One': '1', 'Two': '2'}.get(e, e)

def vt(e):
    """the V-level reading of an entry (literals ascribed: a closed row's `0 = ‖0‖` is ℕ otherwise)"""
    if isinstance(e, tuple):
        if e[0] == 'S': return f'({vt(e[1])} + 1)'
        if e[0] == 'C': return '(' + ' + '.join(['(0 : V)'] + ['1'] * e[1]) + ')' if e[1] > 0 else '(0 : V)'
        if e[0] == 'P': return f'({vt(e[1])} + {vt(e[2])})'
        if e[0] == 'M': return f'({vt(e[1])} * {vt(e[2])})'
    return {'Z': '(0 : V)', 'One': '(1 : V)', 'Two': '(2 : V)'}.get(e, e)

def code_entry(e, env):
    if isinstance(e, tuple):
        if e[0] == 'S': return f'({code_entry(e[1], env)} ^+ (𝟏 : V))'
        if e[0] == 'C': return f'cT {e[1]}'
        if e[0] == 'P': return f'({code_entry(e[1], env)} ^+ {code_entry(e[2], env)})'
        if e[0] == 'M': return f'({code_entry(e[1], env)} ^* {code_entry(e[2], env)})'
    if e == 'Z': return '(𝟎 : V)'
    if e == 'One': return '(𝟏 : V)'
    if e == 'Two': return '((𝟏 : V) ^+ (𝟏 : V))'
    return f'bv {env[e]}'

def fact_entry(e, wit):
    if isinstance(e, tuple):
        if e[0] == 'S': return f'({fact_entry(e[1], wit)} ^+ (𝟏 : V))'
        if e[0] == 'C': return f'(cT {e[1]})'
        if e[0] == 'P': return f'({fact_entry(e[1], wit)} ^+ {fact_entry(e[2], wit)})'
        if e[0] == 'M': return f'({fact_entry(e[1], wit)} ^* {fact_entry(e[2], wit)})'
    if e == 'Z': return '(𝟎 : V)'
    if e == 'One': return '(𝟏 : V)'
    if e == 'Two': return '((𝟏 : V) ^+ (𝟏 : V))'
    w = wit[e]
    return w if ' ' not in w else f'({w})'

def has_arith(e):
    return isinstance(e, tuple) and e[0] in ('P', 'M', 'S')

# ----------------------------------------------------------------------------- Frag.lean
def atom_dsl(a):
    return PREDS[a[1]]['dsl']([dsl(x) for x in a[2]])
def atom_v(a):
    return PREDS[a[1]]['V']([vt(x) for x in a[2]])

def conc_dsl(c):
    if c[0] == 'atom':
        return atom_dsl(c)
    vs, conj = c[1], c[2]
    return f'∃ {" ".join(vs)}, ' + ' ∧ '.join(atom_dsl(it) for it in conj)
def conc_v(c):
    if c[0] == 'atom':
        return atom_v(c)
    vs, conj = c[1], c[2]
    return f'∃ {" ".join(vs)}, ' + ' ∧ '.join(atom_v(it) for it in conj)

def wname(v):
    return 'w' + v.replace("'", "p").replace('₁', '1').replace('₂', '2')

frag = []
def F(s=''):
    frag.append(s)

def gen_frag_row(group, name, binders, ants, conc, proof, doc):
    m = len(binders)
    body = ' → '.join([atom_dsl(a) for a in ants] + [conc_dsl(conc)])
    text = f'“{" ".join(binders)}. {body}”' if binders else f'“{body}”'
    F(f'/-- {doc} -/' if doc else f'/-- `{name}`. -/')
    F(f'noncomputable def {name}B : ArithmeticSemisentence {m} :=')
    F(f'  {text}')
    F(f'noncomputable def {name} : ArithmeticSentence := ∀¹* {name}B')
    vstmt = ' → '.join([atom_v(a) for a in ants] + [conc_v(conc)])
    if binders:
        vstmt = f'∀ {" ".join(binders)} : V, {vstmt}'
    simps = []
    for a in ants + ([conc] if conc[0] == 'atom' else conc[2]):
        for s in PREDS[a[1]]['simps']:
            if s not in simps:
                simps.append(s)
    F(f'lemma models_{name} : V↓[ℒₒᵣ] ⊧ {name} ↔ {vstmt} := by')
    # at `m = 0` (a closed row) `simp` HANGS with `Matrix.vecForall_iff` or a `.defined.iff` lemma in
    # its set; the bare `models_iff` set closes those rows (the `Defined` instances fire on their own)
    if binders:
        F(f'  simp [{", ".join([name, name + "B", "models_iff", "Matrix.vecForall_iff"] + simps)}]')
    else:
        F(f'  simp [{name}, {name}B, models_iff]')
    if proof is None:
        lam = ' '.join(['_'] * m + [f'h{i}' for i in range(1, len(ants) + 1)])
        proof = f'fun {lam} ↦ by subst_vars; first | rfl | assumption | trivial'
    elif isinstance(proof, tuple) and proof[0] == 'by':
        lam = ' '.join(['_'] * m + [f'h{"₀₁₂₃₄₅₆₇₈₉"[i]}' if i < 10 else f'h{i}' for i in range(1, len(ants) + 1)])
        proof = (f'fun {lam} ↦ by {proof[1]}') if lam else f'by {proof[1]}'
    F(f'theorem pa_proves_{name} : 𝗣𝗔 ⊢ {name} :=')
    F(f'  Lib.pa_proves_of_models fun _ _ _ ↦ models_{name}.mpr {proof}')
    F(f'theorem lib_{name} : Lib {name} := Lib.of_pa pa_proves_{name}')
    F()

GROUP_TITLES = {
  'copy': 'A. Copy-in: equality and the congruence rows (§3.3)',
  'ident': 'B. Identification: the injectivity rows (§3.5)',
  'fun': 'C. Functionality (`pinSteps`, §4.10(i))',
  'sets': 'D. Sets: extensionality and `setShift` on a chain (§3.4, §4.5)',
  'fstIdx': 'E. The ten `fstIdx<Tag>` rows (§4.0 step 2)',
  'nodes': 'F. The top: `dlenDef`, `proof`, `instB`, `gBudget`, `‖·‖`, the `bnum` certification (§7.1)',
  'lengths': 'G. Lengths: `termLenVec`/`listSum` bottom-up, the atom lengths with universal `M, s` (§3.6)',
  'cert': 'H. Certification: `neg`/`shift`/`subst`/`free` bottom-up, the term level, `qVec` (§3.6)',
  'num': 'I. Numerals N4/N5 (§2.4), in the DSL',
  'axm': 'J. `axm`(ii): `qqAlls`, `bv`, `termBV`, `listMax`, `fvarVec`, the `max`/`−` glue (§4.10(ii))',
}

def gen_frag():
    F('namespace ArithS')
    F()
    F('open FFL FFL.FirstOrder Arithmetic Bootstrapping')
    F('open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic')
    F('open PeanoMinus ISigma0 ISigma1')
    F('open LAct')
    F()
    F('variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]')
    F()
    F('-- the generated closing tactic `first | rfl | assumption | trivial` trips the unused/unreachable-tactic linters')
    F('set_option linter.unusedTactic false')
    F('set_option linter.unreachableTactic false')
    F('set_option linter.unusedSimpArgs false')
    F()
    F('/-- `setShift (insert x s) = insert (shift x) (setShift s)` (`mem_ext` + `mem_setShift_iff`). -/')
    F('lemma setShift_insert (x s : V) : setShift LAct (insert x s) = insert (shift LAct x) (setShift LAct s) := by')
    F('  apply mem_ext; intro y')
    F('  simp only [mem_setShift_iff, mem_bitInsert_iff]')
    F('  constructor')
    F('  · rintro ⟨z, hz | hz, rfl⟩')
    F('    · left; rw [hz]')
    F('    · right; exact ⟨z, hz, rfl⟩')
    F('  · rintro (rfl | ⟨z, hz, rfl⟩)')
    F('    · exact ⟨x, Or.inl rfl, rfl⟩')
    F('    · exact ⟨z, Or.inr hz, rfl⟩')
    F()
    F('/-- `setShift 0 = 0` (`setShift_empty` with `∅ = 0`). -/')
    F('lemma setShift_zero : setShift LAct (0 : V) = 0 := setShift_empty')
    F()
    cur = None
    for (group, name, binders, ants, conc, proof, doc) in selected():
        if group != cur:
            F(f'/-! ### {GROUP_TITLES[group]} -/')
            F()
            cur = group
        gen_frag_row(group, name, binders, ants, conc, proof, doc)
    F('end ArithS')

# ----------------------------------------------------------------------------- RowInstB.lean
out = []
def emit(s=''):
    out.append(s)

def mem_term(proofs):
    t = 'List.forall_mem_nil _'
    for p in reversed(proofs):
        t = f'List.forall_mem_cons.mpr ⟨{p}, {t}⟩'
    return f'({t})'

def used_preds():
    ks = []
    for r in selected():
        for a in r[3] + ([r[4]] if r[4][0] == 'atom' else r[4][2]):
            if a[1] not in ks:
                ks.append(a[1])
    return ks

def gen_preds():
    emit('/-! ## 2. The predicate codes and the canonical fact codes not in `RowInst.lean`/`Chain.lean` -/')
    emit()
    emit('section facts')
    emit()
    for key in used_preds():
        d = PREDS[key]
        have = d['have']
        P, Fn, args, ar = d['P'], d['F'], d['args'], d['ar']
        if have == ALL:
            continue
        if 'P' not in have:
            emit(f'/-- The code of `{key}` (arity {ar}). -/')
            emit(f'noncomputable def {P} : V := ⌜Semiformula.lMap emb {d["sem"]}⌝')
        if 'isSem' not in have:
            emit(f'lemma isSemiformula_{P} : IsSemiformula LAct (({ar} : ℕ) : V) {P} := Sentence.quote_isSemiformula _')
        if 'shift' not in have:
            emit(f'lemma shift_{P} : shift LAct ({P} : V) = {P} := shift_quote_sentence _')
        if 'fvOcc' not in have:
            emit(f'lemma fvOccF_{P} : fvOccF LAct ({P} : V) = 0 := fvOccF_quote_sentence _')
        emit()
    emit("/-! ### The facts: `subst (listToVec [witnesses]) P` in the predicate's own variable order -/")
    emit()
    for key in used_preds():
        d = PREDS[key]
        have = d['have']
        P, Fn, args, ar = d['P'], d['F'], d['args'], d['ar']
        if have == ALL:
            continue
        argstr = ' '.join(args)
        hyps = ' '.join(f'(h{a} : IsSemiterm LAct 0 {a})' for a in args)
        binder = '{' + ' '.join(args) + ' : V}'
        lst = ', '.join(args)
        if 'Fdef' not in have:
            emit(f'noncomputable def {Fn} ({argstr} : V) : V := subst LAct (listToVec [{lst}]) {P}')
        if 'isFormula' not in have:
            emit(f'lemma isFormula_{Fn} {binder} {hyps} : IsFormula LAct ({Fn} {argstr}) :=')
            emit(f'  isFormula_fact isSemiformula_{P} _ rfl {mem_term([f"h{a}" for a in args])}')
        if 'shiftF' not in have:
            emit(f'lemma shift_{Fn} {binder} {hyps} :')
            emit(f'    shift LAct ({Fn} {argstr}) = {Fn} {" ".join(f"(termShift LAct {a})" for a in args)} := by')
            emit(f'  unfold {Fn}')
            emit(f'  rw [shift_subst_listToVec [{lst}] isSemiformula_{P} shift_{P} (n := 0) {mem_term([f"h{a}" for a in args])}]')
            emit(f'  rfl')
        if 'len' not in have:
            lhyps = ' '.join(f'(hl{a} : termLen LAct {a} ≤ B)' for a in args)
            emit(f'lemma formulaLen_{Fn}_le {{B : V}} (hB : 1 ≤ B) {binder} {hyps} {lhyps} :')
            emit(f'    formulaLen LAct ({Fn} {argstr}) ≤ formulaLen LAct ({P} : V) * B :=')
            emit(f'  formulaLen_fact_le hB isSemiformula_{P} _ rfl {mem_term([f"⟨h{a}, hl{a}⟩" for a in args])}')
        if 'occ' not in have:
            ohyps = ' '.join(f'(ho{a} : fvOcc LAct {a} ≤ M)' for a in args)
            emit(f'lemma fvOccF_{Fn}_le {{M : V}} {binder} {hyps} {ohyps} :')
            emit(f'    fvOccF LAct ({Fn} {argstr}) ≤ bvOccF LAct ({P} : V) * M :=')
            emit(f'  fvOccF_fact_le isSemiformula_{P} fvOccF_{P} _ rfl {mem_term([f"⟨h{a}, ho{a}⟩" for a in args])}')
        emit()
    emit('end facts')
    emit()

# ---- trees (as in gen_rowinst.py)
def tree_of(conc, env):
    if conc[0] == 'atom':
        return ('leaf', conc[1], conc[2], dict(env))
    vs, conj = conc[1], conc[2]
    a = len(vs)
    env2 = {k: v + a for k, v in env.items()}
    for i, v in enumerate(vs):
        env2[v] = a - 1 - i
    t = tree_of(conj[-1], env2)
    for it in reversed(conj[:-1]):
        t = ('and', tree_of(it, env2), t)
    for _ in range(a):
        t = ('ex', t)
    return t

def code_bv(t):
    if t[0] == 'leaf':
        _, pred, args, env = t
        return f'subst LAct (listToVec [{", ".join(code_entry(x, env) for x in args)}]) {PREDS[pred]["P"]}'
    if t[0] == 'and':
        r = code_bv(t[2])
        return f'{code_bv(t[1])} ^⋏ ({r})' if t[2][0] != 'leaf' else f'{code_bv(t[1])} ^⋏ {r}'
    return f'^∃ ({code_bv(t[1])})' if t[1][0] != 'leaf' else f'^∃ {code_bv(t[1])}'

def semif(t):
    if t[0] == 'leaf':
        return f'isSemiformula_substRow isSemiformula_{PREDS[t[1]]["P"]} _ (by rfl) (by row_entriesB)'
    if t[0] == 'and':
        return f'IsSemiformula.and.mpr ⟨{semif(t[1])}, {semif(t[2])}⟩'
    return f'isSemiformula_exs_cast ({semif(t[1])})'

def fact_code(pred, args, wit):
    return f'{PREDS[pred]["F"]} {" ".join(fact_entry(x, wit) for x in args)}'

def conj_facts(items, wit):
    codes = [fact_code(it[1], it[2], wit) for it in items]
    s = codes[-1]
    for c in reversed(codes[:-1]):
        s = f'{c} ^⋏ ({s})'
    return s

def leaves(t):
    if t[0] == 'leaf':
        return [t]
    if t[0] == 'and':
        return leaves(t[1]) + leaves(t[2])
    return leaves(t[1])

def dedupe(xs):
    seen = set(); r = []
    for x in xs:
        if x not in seen:
            seen.add(x); r.append(x)
    return r

def gen_row(name, binders, ants, conc):
    m = len(binders)
    env = {v: i for i, v in enumerate(binders)}
    R = f'row_{name}'
    is_ex = conc[0] == 'ex'
    ant_trees = [tree_of(a_, env) for a_ in ants]
    Pset = set()
    unf_extra = set()
    for t in ant_trees + [tree_of(conc, env)]:
        for l in leaves(t):
            Pset.add(PREDS[l[1]]['P'])
            unf_extra.update(PREDS[l[1]]['unfold'])
    Punfold = ' '.join(sorted(Pset) + sorted(unf_extra))
    emit(f'/-! ### `{name}` — `“{" ".join(binders)}{"." if binders else ""} …”`, `m = {m}` -/')
    emit()
    emit(f'noncomputable def {R}_as : List V := [{", ".join(code_bv(t) for t in ant_trees)}]')
    if not is_ex:
        ctree = tree_of(conc, env)
        emit(f'noncomputable def {R}_c : V := {code_bv(ctree)}')
        unf_c = f'{R}_c'
    else:
        vs, conj = conc[1], conc[2]
        a1 = len(vs)
        full = tree_of(conc, env)
        body = full
        for _ in range(a1):
            body = body[1]
        emit(f'noncomputable def {R}_body : V := {code_bv(body)}')
        unf_body = f'{R}_body'
        emit(f'noncomputable def {R}_R : V := {"^∃ " * (a1 - 1)}{R}_body')
        emit(f'noncomputable def {R}_c : V := ^∃ {R}_R')
        unf_c = f'{R}_c {R}_R {unf_body}'
    emit()
    emit(f'theorem quote_row_{name} : (⌜Semiformula.lMap emb {name}B⌝ : V) = impChain LAct {R}_as {R}_c := by')
    emit(f'  unfold {name}B {R}_as {unf_c} {Punfold}')
    emit(f'  all_goals row_shapeB')
    emit()
    lvl = f'(({m} : ℕ) : V)'
    emit(f'lemma isSemiformula_{name}_as : ∀ A ∈ {R}_as, IsSemiformula LAct {lvl} A := by')
    emit(f'  unfold {R}_as')
    emit(f'  exact {mem_term([semif(t) for t in ant_trees])}')
    emit(f'lemma isSemiformula_{name}_c : IsSemiformula LAct {lvl} {R}_c := by')
    emit(f'  unfold {unf_c}')
    emit(f'  exact {semif(tree_of(conc, env))}')
    if is_ex:
        Rtree = full[1]
        emit(f'lemma isSemiformula_{name}_R : IsSemiformula LAct (({m + 1} : ℕ) : V) {R}_R := by')
        emit(f'  unfold {R}_R {unf_body}')
        emit(f'  exact {semif(Rtree)}')
        emit(f'lemma isSemiformula_{name}_body : IsSemiformula LAct (({m + a1} : ℕ) : V) {R}_body := by')
        emit(f'  unfold {unf_body}')
        emit(f'  exact {semif(body)}')
        emit(f'lemma {R}_R_eq : ({R}_R : V) = exsIter {a1 - 1} {R}_body := rfl')
    emit()
    wits = [wname(v) for v in reversed(binders)]
    wit = {v: wname(v) for v in binders}
    binder = ('{' + ' '.join(wits) + ' : V} ') if wits else ''
    hyps = ' '.join(f'(h{w} : IsSemiterm LAct 0 {w})' for w in wits)
    es = ('[' + ', '.join(wits) + ']') if wits else '([] : List V)'
    hes_term = mem_term([f'h{w}' for w in wits])
    ant_facts = [fact_code(a_[1], a_[2], wit) for a_ in ants]
    emit(f'/-- `{name}` at the witnesses `{es}` (the DSL variables right-to-left). -/')
    if not is_ex:
        emit(f'lemma inst_{name} {binder}{hyps} :')
        emit(f'    {R}_as.map (instOuter LAct {es}) = [{", ".join(ant_facts)}] ∧')
        emit(f'    instOuter LAct {es} {R}_c = {fact_code(conc[1], conc[2], wit)} := by')
        emit(f'  have hes : ∀ e ∈ ({es} : List V), IsSemiterm LAct 0 e := {hes_term}')
        emit(f'  unfold {R}_as {R}_c')
        emit(f'  simp only [List.map_cons, List.map_nil]')
        pieces = dedupe([code_bv(t) + '|' + PREDS[t[1]]['P'] for t in ant_trees + [tree_of(conc, env)]])
        rws = ', '.join(f'instOuter_subst_listToVec _ isSemiformula_{pc.split("|")[1]} (by rfl) _ hes (by row_entriesB)' for pc in pieces)
        emit(f'  rw [{rws}]')
        emit(f'  all_goals try row_entries_simpB')
        emit(f'  row_finish')
        emit()
        return
    vs, conj = conc[1], conc[2]
    a1 = len(vs)
    def sh(e, k):
        return f'termShift LAct {e}' if k == 1 else f'(termShift LAct)^[{k}] {e}'
    wit1 = {v: sh(wname(v), a1) for v in binders}
    for i, v in enumerate(vs):
        wit1[v] = f'^&(({a1 - 1 - i} : ℕ) : V)'
    emit(f'lemma inst_{name} {binder}{hyps} :')
    emit(f'    {R}_as.map (instOuter LAct {es}) = [{", ".join(ant_facts)}] ∧')
    rhs = conj_facts(conj, wit1)
    emit(f'    freeIter LAct {a1} (instOuterAt LAct {a1} {es} {R}_body) = {rhs} := by')
    emit(f'  have hes : ∀ e ∈ ({es} : List V), IsSemiterm LAct 0 e := {hes_term}')
    emit(f'  unfold {R}_as {unf_body}')
    emit(f'  simp only [List.map_cons, List.map_nil]')
    if ant_trees:
        pieces = dedupe([code_bv(t) + '|' + PREDS[t[1]]['P'] for t in ant_trees])
        rws = ', '.join(f'instOuter_subst_listToVec _ isSemiformula_{pc.split("|")[1]} (by rfl) _ hes (by row_entriesB)' for pc in pieces)
        emit(f'  rw [{rws}]')
    emit(f'  refine ⟨by ((try row_entries_simpB); row_finish), ?_⟩')
    steps = []
    def push_inst(t, k):
        if t[0] == 'and':
            steps.append(f'instOuterAt_and {k} _ ({semif(t[1])}) ({semif(t[2])}) hes')
            push_inst(t[1], k); push_inst(t[2], k)
        elif t[0] == 'ex':
            steps.append(f'instOuterAt_exs {k} _ ({semif(t[1])}) hes')
            push_inst(t[1], k + 1)
    push_inst(body, a1)
    leaf_rws = dedupe([f'instOuterAt_subst_listToVec {a1} _ isSemiformula_{PREDS[l[1]]["P"]} (by rfl) _ hes (by row_entriesB)|{code_bv(l)}'
                       for l in leaves(body)])
    leaf_rws = [x.split('|')[0] for x in leaf_rws]
    emit(f'  · rw [{", ".join(steps + leaf_rws)}]')
    emit(f'    row_entries_simpB')
    steps = []
    def push_free(t):
        if t[0] == 'and':
            steps.append(f'freeIter_and {a1} ({semif(t[1])}) ({semif(t[2])})')
            push_free(t[1]); push_free(t[2])
    push_free(body)
    lr = dedupe([f'freeIter_subst_listToVec\' {a1} _ isSemiformula_{PREDS[l[1]]["P"]} shift_{PREDS[l[1]]["P"]} (by rfl) (by row_entriesB)|{l[1]}{l[2]}'
                 for l in leaves(body)])
    lr = [x.split('|')[0] for x in lr]
    emit(f'    rw [{", ".join(steps + lr)}]')
    ent = []
    used_bv = set(); used_w = set()
    for l in leaves(body):
        for x in l[2]:
            base = x[1] if isinstance(x, tuple) and x[0] == 'S' else x
            if isinstance(base, tuple) or base in ('Z', 'One', 'Two'):
                continue
            if base in binders:
                used_w.add(base)
            else:
                used_bv.add(l[3][base])
    for i in sorted(used_bv):
        ent.append(f'freeIterT_bv0 {a1} {i} (by norm_num)')
    for v in sorted(used_w):
        ent.append(f'freeIterT_closed 0 h{wname(v)} {a1}')
    zs = [f'freeIterT_closed 0 (isSemiterm_qqZero_LAct 0) {a1}', f'iterate_termShift_qqZero {a1}'] if any(x == 'Z' for l in leaves(body) for x in l[2]) else []
    emit(f'    simp only [List.map_cons, List.map_nil]')
    if ent + zs:
        emit(f'    rw [{", ".join(ent + zs)}]')
    emit(f'    try rfl')
    emit()

def gen_rowinstb():
    gen_preds()
    emit('/-! ## 3. The rows: pieces, row-shape, formula-ness, instantiation -/')
    emit()
    emit('section rows')
    emit()
    cur = None
    for (group, name, binders, ants, conc, proof, doc) in selected():
        if group != cur:
            emit(f'/-! ## {GROUP_TITLES[group]} -/')
            emit()
            cur = group
        gen_row(name, binders, ants, conc)
    emit('end rows')
    emit()

# ----------------------------------------------------------------------------- the header table
def table():
    lines = ['| group | delivered rows |', '|---|---|']
    cur = None; acc = []
    for (group, name, *_r) in ROWS:
        if group != cur:
            if cur is not None:
                lines.append(f'| {cur} | {", ".join(f"`{n}`" for n in acc)} |')
            cur = group; acc = []
        acc.append(name)
    lines.append(f'| {cur} | {", ".join(f"`{n}`" for n in acc)} |')
    return '\n'.join(lines)

gen_frag()
gen_rowinstb()
import os
HERE = os.path.dirname(os.path.abspath(__file__))
fh = open(os.path.join(HERE, 'Frag.lean.head')).read().replace('<<TABLE>>', table())
open(sys.argv[1], 'w').write(fh + '\n'.join(frag) + '\n')
rh = open(os.path.join(HERE, 'RowInstB.lean.head')).read()
open(sys.argv[2], 'w').write(rh + '\n'.join(out) + '\nend ArithS\n')
print('rows:', len(selected()), 'of', len(ROWS))
