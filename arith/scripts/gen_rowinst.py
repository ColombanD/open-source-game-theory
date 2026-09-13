#!/usr/bin/env python3
"""Generator for arith/ArithS/Necessitation/RowInst.lean (row-shape + instantiation lemmas).

usage: gen_rowinst.py <out.lean> [subset]   (reads <out.lean>.head as the header)

Row table: name, binders (DSL order, x0 = #0), antecedents [(pred, args)], conclusion.
Args: a binder/existential variable name, ('S', name) for `name + 1`, 'Z' for the literal `0`,
'One' for the literal `1`, ('C', k) for the chain literal `0 + 1 + ... + 1` (cTT k).
Conclusion: ('atom', pred, args) | ('ex', [vars], [conjuncts]) where the last conjunct may be
a nested ('ex', ...).  Conjunctions are right-associated (the DSL's `∧`).
"""
import sys

# pred key -> (Lean semisentence, arity, Pname, factname, def arg names, existing?)
PREDS = {
  'pi':       ('(↑(isSemiformula LAct).pi : ArithmeticSemisentence 2)', 2, 'Ppi', 'piFact', ['n', 'a'], True),
  'sigma':    ('(↑(isSemiformula LAct).sigma : ArithmeticSemisentence 2)', 2, 'Psigma', 'sigmaFact', ['n', 'a'], True),
  'qqAnd':    ('(↑qqAndDef : ArithmeticSemisentence 3)', 3, 'Pand', 'andFact', ['z', 'a', 'b'], True),
  'qqOr':     ('(↑qqOrDef : ArithmeticSemisentence 3)', 3, 'Por', 'orFact', ['z', 'a', 'b'], False),
  'qqAll':    ('(↑qqAllDef : ArithmeticSemisentence 2)', 2, 'Pall', 'allFact', ['q', 'p'], False),
  'qqExs':    ('(↑qqExsDef : ArithmeticSemisentence 2)', 2, 'Pexs', 'exsFact', ['q', 'p'], False),
  'qqRel':    ('(↑qqRelDef : ArithmeticSemisentence 4)', 4, 'Prel', 'relFact', ['p', 'k', 'R', 'v'], False),
  'qqNRel':   ('(↑qqNRelDef : ArithmeticSemisentence 4)', 4, 'Pnrel', 'nrelFact', ['p', 'k', 'R', 'v'], False),
  'qqVerum':  ('(↑qqVerumDef : ArithmeticSemisentence 1)', 1, 'Pverum', 'verumFact', ['p'], False),
  'qqFalsum': ('(↑qqFalsumDef : ArithmeticSemisentence 1)', 1, 'Pfalsum', 'falsumFact', ['p'], False),
  'qqFunc':   ('(↑qqFuncDef : ArithmeticSemisentence 4)', 4, 'Pfunc', 'funcFact', ['t', 'k', 'f', 'v'], False),
  'qqBvar':   ('(↑qqBvarDef : ArithmeticSemisentence 2)', 2, 'Pbvar', 'bvarFact', ['t', 'z'], False),
  'qqFvar':   ('(↑qqFvarDef : ArithmeticSemisentence 2)', 2, 'Pfvar', 'fvarFact', ['t', 'x'], False),
  'adjoin':   ('(↑adjoinDef : ArithmeticSemisentence 3)', 3, 'Padjoin', 'adjFact', ['w', 't', 'v'], False),
  'tpi':      ('(↑(isSemiterm LAct).pi : ArithmeticSemisentence 2)', 2, 'PtPi', 'tPiFact', ['n', 't'], False),
  'tsigma':   ('(↑(isSemiterm LAct).sigma : ArithmeticSemisentence 2)', 2, 'PtSigma', 'tSigmaFact', ['n', 't'], False),
  'tvpi':     ('(↑(isSemitermVec LAct).pi : ArithmeticSemisentence 3)', 3, 'PtvPi', 'tvPiFact', ['k', 'n', 'v'], False),
  'tvsigma':  ('(↑(isSemitermVec LAct).sigma : ArithmeticSemisentence 3)', 3, 'PtvSigma', 'tvSigmaFact', ['k', 'n', 'v'], False),
  'utvpi':    ('(↑(isUTermVec LAct).pi : ArithmeticSemisentence 2)', 2, 'PutvPi', 'utvPiFact', ['k', 'v'], False),
  'utvsigma': ('(↑(isUTermVec LAct).sigma : ArithmeticSemisentence 2)', 2, 'PutvSigma', 'utvSigmaFact', ['k', 'v'], False),
  'isRel':    ('(↑LAct.isRel : ArithmeticSemisentence 2)', 2, 'PisRel', 'isRelFact', ['k', 'R'], False),
  'isFunc':   ('(↑LAct.isFunc : ArithmeticSemisentence 2)', 2, 'PisFunc', 'isFuncFact', ['k', 'f'], False),
  'lt':       ('(Rewriting.emb (Semiformula.Operator.LT.lt : Semiformula.Operator ℒₒᵣ 2).sentence : ArithmeticSemisentence 2)', 2, 'Plt', 'ltFact', ['a', 'b'], False),
  'negG':     ('(↑(negGraph LAct) : ArithmeticSemisentence 2)', 2, 'PnegG', 'negFact', ['y', 'p'], False),
  'shiftG':   ('(↑(shiftGraph LAct) : ArithmeticSemisentence 2)', 2, 'PshiftG', 'shiftFact', ['y', 'p'], False),
  'substsG':  ('(↑(substsGraph LAct) : ArithmeticSemisentence 3)', 3, 'PsubstsG', 'substFact', ['y', 'w', 'p'], False),
  'substs1G': ('(↑(substs1Graph LAct) : ArithmeticSemisentence 3)', 3, 'Psubsts1G', 'substs1Fact', ['y', 't', 'p'], False),
  'freeG':    ('(↑(freeGraph LAct) : ArithmeticSemisentence 2)', 2, 'PfreeG', 'freeFact', ['y', 'p'], False),
  'qVecG':    ('(↑(qVecGraph LAct) : ArithmeticSemisentence 2)', 2, 'PqVecG', 'qVecFact', ['u', 'w'], False),
  'tsvG':     ('(↑(termSubstVecGraph LAct) : ArithmeticSemisentence 4)', 4, 'PtsvG', 'tsvFact', ['u', 'k', 'w', 'v'], False),
  'tshvG':    ('(↑(termShiftVecGraph LAct) : ArithmeticSemisentence 3)', 3, 'PtshvG', 'tshvFact', ['u', 'k', 'v'], False),
}

def A(pred, *args):
    return ('atom', pred, list(args))
def EX(vs, conj):
    return ('ex', vs, conj)
S = lambda v: ('S', v)
C = lambda k: ('C', k)

ROWS = [
  # ---- totality rows (Formulas / Sets)
  ('qqRelTotal',   ['v','R','k'], [], EX(['p'], [A('qqRel','p','k','R','v')])),
  ('qqNRelTotal',  ['v','R','k'], [], EX(['p'], [A('qqNRel','p','k','R','v')])),
  ('qqVerumTotal', [], [], EX(['p'], [A('qqVerum','p')])),
  ('qqFalsumTotal',[], [], EX(['p'], [A('qqFalsum','p')])),
  ('qqAndTotal',   ['q','p'], [], EX(['r'], [A('qqAnd','r','p','q')])),
  ('qqOrTotal',    ['q','p'], [], EX(['r'], [A('qqOr','r','p','q')])),
  ('qqAllTotal',   ['p'], [], EX(['q'], [A('qqAll','q','p')])),
  ('qqExsTotal',   ['p'], [], EX(['q'], [A('qqExs','q','p')])),
  ('qqFuncTotal',  ['v','f','k'], [], EX(['t'], [A('qqFunc','t','k','f','v')])),
  ('qqBvarTotal',  ['z'], [], EX(['t'], [A('qqBvar','t','z')])),
  ('qqFvarTotal',  ['x'], [], EX(['t'], [A('qqFvar','t','x')])),
  ('adjoinTotal',  ['v','t'], [], EX(['w'], [A('adjoin','w','t','v')])),
  ('negTotal',     ['p'], [], EX(['y'], [A('negG','y','p')])),
  ('shiftTotal',   ['p'], [], EX(['q'], [A('shiftG','q','p')])),
  ('substsTotal',  ['p','w'], [], EX(['y'], [A('substsG','y','w','p')])),
  ('substs1Total', ['p','t'], [], EX(['y'], [A('substs1G','y','t','p')])),
  ('freeTotal',    ['p'], [], EX(['q'], [A('freeG','q','p')])),
  ('qVecTotal',    ['w'], [], EX(['u'], [A('qVecG','u','w')])),
  ('termSubstVecTotal', ['v','w','k'], [], EX(['u'], [A('tsvG','u','k','w','v')])),
  ('termShiftVecTotal', ['v','k'], [], EX(['u'], [A('tshvG','u','k','v')])),
  # ---- formation rows
  ('isSemiformulaRel',   ['p','v','R','k','n'], [A('isRel','k','R'), A('tvpi','k','n','v'), A('qqRel','p','k','R','v')], A('sigma','n','p')),
  ('isSemiformulaNRel',  ['p','v','R','k','n'], [A('isRel','k','R'), A('tvpi','k','n','v'), A('qqNRel','p','k','R','v')], A('sigma','n','p')),
  ('isSemiformulaVerum', ['p','n'], [A('qqVerum','p')], A('sigma','n','p')),
  ('isSemiformulaFalsum',['p','n'], [A('qqFalsum','p')], A('sigma','n','p')),
  ('isSemiformulaAnd',   ['r','q','p','n'], [A('pi','n','p'), A('pi','n','q'), A('qqAnd','r','p','q')], A('sigma','n','r')),
  ('isSemiformulaOr',    ['r','q','p','n'], [A('pi','n','p'), A('pi','n','q'), A('qqOr','r','p','q')], A('sigma','n','r')),
  ('isSemiformulaAll',   ['q','p','n'], [A('pi',S('n'),'p'), A('qqAll','q','p')], A('sigma','n','q')),
  ('isSemiformulaExs',   ['q','p','n'], [A('pi',S('n'),'p'), A('qqExs','q','p')], A('sigma','n','q')),
  ('isSemiformulaNeg',   ['y','p','n'], [A('pi','n','p'), A('negG','y','p')], A('sigma','n','y')),
  ('isSemiformulaShift', ['y','p','n'], [A('pi','n','p'), A('shiftG','y','p')], A('sigma','n','y')),
  ('isSemiformulaSubst', ['y','w','p','m','n'], [A('pi','n','p'), A('tvpi','n','m','w'), A('substsG','y','w','p')], A('sigma','m','y')),
  ('isSemiformulaSubsts1', ['y','p','t','n'], [A('tpi','n','t'), A('pi','One','p'), A('substs1G','y','t','p')], A('sigma','n','y')),
  ('isFormulaFree',      ['y','p'], [A('pi','One','p'), A('freeG','y','p')], A('sigma','Z','y')),
  ('isSemitermFunc',     ['t','v','f','k','n'], [A('isFunc','k','f'), A('tvpi','k','n','v'), A('qqFunc','t','k','f','v')], A('tsigma','n','t')),
  ('isSemitermBvar',     ['t','z','n'], [A('lt','z','n'), A('qqBvar','t','z')], A('tsigma','n','t')),
  ('isSemitermFvar',     ['t','x','n'], [A('qqFvar','t','x')], A('tsigma','n','t')),
  ('isSemitermVecNil',   ['n'], [], A('tvsigma','Z','n','Z')),
  ('isSemitermVecAdjoin',['u','t','w','n','k'], [A('tvpi','k','n','w'), A('tpi','n','t'), A('adjoin','u','t','w')], A('tvsigma',S('k'),'n','u')),
  # ---- bridges (LAct)
  ('isSemiformulaSigmaPi',     ['p','n'], [A('sigma','n','p')], A('pi','n','p')),
  ('isSemitermSigmaPiLAct',    ['t','n'], [A('tsigma','n','t')], A('tpi','n','t')),
  ('isSemitermVecSigmaPiLAct', ['v','n','k'], [A('tvsigma','k','n','v')], A('tvpi','k','n','v')),
  ('isUTermVecSigmaPiLAct',    ['v','k'], [A('utvsigma','k','v')], A('utvpi','k','v')),
  # ---- walk rows
  ('zeroLtSucc', ['y'], [], A('lt','Z',S('y'))),
  ('succLtSucc', ['y','x'], [A('lt','x','y')], A('lt',S('x'),S('y'))),
  ('isRelConst_eq',   [], [], A('isRel',C(2),C(0))),
  ('isRelConst_lt',   [], [], A('isRel',C(2),C(1))),
  ('isFuncConst_zero',[], [], A('isFunc',C(0),C(0))),
  ('isFuncConst_one', [], [], A('isFunc',C(0),C(1))),
  ('isFuncConst_add', [], [], A('isFunc',C(2),C(0))),
  ('isFuncConst_mul', [], [], A('isFunc',C(2),C(1))),
  ('isFuncConst_cC',  [], [], A('isFunc',C(0),C(2))),
  ('isFuncConst_cD',  [], [], A('isFunc',C(0),C(3))),
  ('isUTermVecOfSemitermVecLAct', ['v','n','k'], [A('tvpi','k','n','v')], A('utvsigma','k','v')),
  ('isSemitermVecQVec', ['u','w','m','n'], [A('tvpi','n','m','w'), A('qVecG','u','w')], A('tvsigma',S('n'),S('m'),'u')),
  ('substs1Substs', ['y','w','t','p'], [A('adjoin','w','t','Z'), A('substs1G','y','t','p')], A('substsG','y','w','p')),
  # ---- commutation rows: neg
  ('negRel',   ['y','r','v','R','k'], [A('isRel','k','R'), A('utvpi','k','v'), A('qqRel','r','k','R','v'), A('negG','y','r')], A('qqNRel','y','k','R','v')),
  ('negNRel',  ['y','r','v','R','k'], [A('isRel','k','R'), A('utvpi','k','v'), A('qqNRel','r','k','R','v'), A('negG','y','r')], A('qqRel','y','k','R','v')),
  ('negVerum', ['y','r'], [A('qqVerum','r'), A('negG','y','r')], A('qqFalsum','y')),
  ('negFalsum',['y','r'], [A('qqFalsum','r'), A('negG','y','r')], A('qqVerum','y')),
  ('negAnd',   ['y','r','q','p','n'], [A('pi','n','p'), A('pi','n','q'), A('qqAnd','r','p','q'), A('negG','y','r')],
               EX(['np','nq'], [A('negG','np','p'), A('negG','nq','q'), A('qqOr','y','np','nq')])),
  ('negOr',    ['y','r','q','p','n'], [A('pi','n','p'), A('pi','n','q'), A('qqOr','r','p','q'), A('negG','y','r')],
               EX(['np','nq'], [A('negG','np','p'), A('negG','nq','q'), A('qqAnd','y','np','nq')])),
  ('negAll',   ['y','r','p','n'], [A('pi',S('n'),'p'), A('qqAll','r','p'), A('negG','y','r')],
               EX(['np'], [A('negG','np','p'), A('qqExs','y','np')])),
  ('negExs',   ['y','r','p','n'], [A('pi',S('n'),'p'), A('qqExs','r','p'), A('negG','y','r')],
               EX(['np'], [A('negG','np','p'), A('qqAll','y','np')])),
  # ---- substs
  ('substsRel',  ['y','r','v','R','k','w'], [A('isRel','k','R'), A('utvpi','k','v'), A('qqRel','r','k','R','v'), A('substsG','y','w','r')],
                 EX(['u'], [A('tsvG','u','k','w','v'), A('qqRel','y','k','R','u')])),
  ('substsNRel', ['y','r','v','R','k','w'], [A('isRel','k','R'), A('utvpi','k','v'), A('qqNRel','r','k','R','v'), A('substsG','y','w','r')],
                 EX(['u'], [A('tsvG','u','k','w','v'), A('qqNRel','y','k','R','u')])),
  ('substsVerum', ['y','r','w'], [A('qqVerum','r'), A('substsG','y','w','r')], A('qqVerum','y')),
  ('substsFalsum',['y','r','w'], [A('qqFalsum','r'), A('substsG','y','w','r')], A('qqFalsum','y')),
  ('substsAnd',  ['y','r','q','p','n','w'], [A('pi','n','p'), A('pi','n','q'), A('qqAnd','r','p','q'), A('substsG','y','w','r')],
                 EX(['sp','sq'], [A('substsG','sp','w','p'), A('substsG','sq','w','q'), A('qqAnd','y','sp','sq')])),
  ('substsOr',   ['y','r','q','p','n','w'], [A('pi','n','p'), A('pi','n','q'), A('qqOr','r','p','q'), A('substsG','y','w','r')],
                 EX(['sp','sq'], [A('substsG','sp','w','p'), A('substsG','sq','w','q'), A('qqOr','y','sp','sq')])),
  ('substsAll',  ['y','r','p','n','w'], [A('pi',S('n'),'p'), A('qqAll','r','p'), A('substsG','y','w','r')],
                 EX(['u','sp'], [A('qVecG','u','w'), A('substsG','sp','u','p'), A('qqAll','y','sp')])),
  ('substsExs',  ['y','r','p','n','w'], [A('pi',S('n'),'p'), A('qqExs','r','p'), A('substsG','y','w','r')],
                 EX(['u','sp'], [A('qVecG','u','w'), A('substsG','sp','u','p'), A('qqExs','y','sp')])),
  # ---- shift
  ('shiftRel',  ['y','r','v','R','k'], [A('isRel','k','R'), A('utvpi','k','v'), A('qqRel','r','k','R','v'), A('shiftG','y','r')],
                EX(['u'], [A('tshvG','u','k','v'), A('qqRel','y','k','R','u')])),
  ('shiftNRel', ['y','r','v','R','k'], [A('isRel','k','R'), A('utvpi','k','v'), A('qqNRel','r','k','R','v'), A('shiftG','y','r')],
                EX(['u'], [A('tshvG','u','k','v'), A('qqNRel','y','k','R','u')])),
  ('shiftVerum', ['y','r'], [A('qqVerum','r'), A('shiftG','y','r')], A('qqVerum','y')),
  ('shiftFalsum',['y','r'], [A('qqFalsum','r'), A('shiftG','y','r')], A('qqFalsum','y')),
  ('shiftAnd',  ['y','r','q','p','n'], [A('pi','n','p'), A('pi','n','q'), A('qqAnd','r','p','q'), A('shiftG','y','r')],
                EX(['sp','sq'], [A('shiftG','sp','p'), A('shiftG','sq','q'), A('qqAnd','y','sp','sq')])),
  ('shiftOr',   ['y','r','q','p','n'], [A('pi','n','p'), A('pi','n','q'), A('qqOr','r','p','q'), A('shiftG','y','r')],
                EX(['sp','sq'], [A('shiftG','sp','p'), A('shiftG','sq','q'), A('qqOr','y','sp','sq')])),
  ('shiftAll',  ['y','r','p','n'], [A('pi',S('n'),'p'), A('qqAll','r','p'), A('shiftG','y','r')],
                EX(['sp'], [A('shiftG','sp','p'), A('qqAll','y','sp')])),
  ('shiftExs',  ['y','r','p','n'], [A('pi',S('n'),'p'), A('qqExs','r','p'), A('shiftG','y','r')],
                EX(['sp'], [A('shiftG','sp','p'), A('qqExs','y','sp')])),
  # ---- free
  ('freeRel',  ['y','r','v','R','k'], [A('isRel','k','R'), A('utvpi','k','v'), A('qqRel','r','k','R','v'), A('freeG','y','r')],
               EX(['fz','w'], [A('qqFvar','fz','Z'), A('adjoin','w','fz','Z'),
                 EX(['u',"u'"], [A('tshvG','u','k','v'), A('tsvG',"u'",'k','w','u'), A('qqRel','y','k','R',"u'")])])),
  ('freeNRel', ['y','r','v','R','k'], [A('isRel','k','R'), A('utvpi','k','v'), A('qqNRel','r','k','R','v'), A('freeG','y','r')],
               EX(['fz','w'], [A('qqFvar','fz','Z'), A('adjoin','w','fz','Z'),
                 EX(['u',"u'"], [A('tshvG','u','k','v'), A('tsvG',"u'",'k','w','u'), A('qqNRel','y','k','R',"u'")])])),
  ('freeVerum', ['y','r'], [A('qqVerum','r'), A('freeG','y','r')], A('qqVerum','y')),
  ('freeFalsum',['y','r'], [A('qqFalsum','r'), A('freeG','y','r')], A('qqFalsum','y')),
  ('freeAnd',  ['y','r','q','p','n'], [A('pi','n','p'), A('pi','n','q'), A('qqAnd','r','p','q'), A('freeG','y','r')],
               EX(['fp','fq'], [A('freeG','fp','p'), A('freeG','fq','q'), A('qqAnd','y','fp','fq')])),
  ('freeOr',   ['y','r','q','p','n'], [A('pi','n','p'), A('pi','n','q'), A('qqOr','r','p','q'), A('freeG','y','r')],
               EX(['fp','fq'], [A('freeG','fp','p'), A('freeG','fq','q'), A('qqOr','y','fp','fq')])),
  ('freeAll',  ['y','r','p','n'], [A('pi',S('n'),'p'), A('qqAll','r','p'), A('freeG','y','r')],
               EX(['fz','w'], [A('qqFvar','fz','Z'), A('adjoin','w','fz','Z'),
                 EX(['u','sp',"sp'"], [A('qVecG','u','w'), A('shiftG','sp','p'), A('substsG',"sp'",'u','sp'), A('qqAll','y',"sp'")])])),
  ('freeExs',  ['y','r','p','n'], [A('pi',S('n'),'p'), A('qqExs','r','p'), A('freeG','y','r')],
               EX(['fz','w'], [A('qqFvar','fz','Z'), A('adjoin','w','fz','Z'),
                 EX(['u','sp',"sp'"], [A('qVecG','u','w'), A('shiftG','sp','p'), A('substsG',"sp'",'u','sp'), A('qqExs','y',"sp'")])])),
]

SUBSET = None
if len(sys.argv) > 2 and sys.argv[2] == 'subset':
    SUBSET = {'qqAndTotal', 'isSemiformulaAnd', 'zeroLtSucc', 'succLtSucc', 'isRelConst_eq', 'negAnd',
              'isSemiformulaAll', 'isSemitermVecNil', 'freeAll', 'qqVerumTotal', 'isSemiformulaSubsts1',
              'substsAll'}

def wname(v):
    return 'w' + v.replace("'", "p")

out = []
def emit(s=''):
    out.append(s)

def mem_term(proofs):
    """∀ x ∈ [..], Q x from a list of proofs"""
    t = 'List.forall_mem_nil _'
    for p in reversed(proofs):
        t = f'List.forall_mem_cons.mpr ⟨{p}, {t}⟩'
    return f'({t})'

# ------------------------------------------------------------------ predicates and facts
def gen_preds():
    emit('/-! ## 2. The predicate codes and the canonical fact codes -/')
    emit()
    emit('section facts')
    emit()
    for key, (sem, ar, P, F, args, existing) in PREDS.items():
        if not existing:
            emit(f'/-- The code of `{key}` (arity {ar}). -/')
            emit(f'noncomputable def {P} : V := ⌜Semiformula.lMap emb {sem}⌝')
            emit(f'lemma isSemiformula_{P} : IsSemiformula LAct (({ar} : ℕ) : V) {P} := Sentence.quote_isSemiformula _')
            emit(f'lemma shift_{P} : shift LAct ({P} : V) = {P} := shift_quote_sentence _')
        emit(f'lemma fvOccF_{P} : fvOccF LAct ({P} : V) = 0 := fvOccF_quote_sentence _')
        emit()
    emit("/-! ### The facts: `subst (listToVec [witnesses]) P` in the predicate's own variable order -/")
    emit()
    for key, (sem, ar, P, F, args, existing) in PREDS.items():
        argstr = ' '.join(args)
        hyps = ' '.join(f'(h{a} : IsSemiterm LAct 0 {a})' for a in args)
        binder = '{' + ' '.join(args) + ' : V}'
        lst = ', '.join(args)
        if not existing:
            emit(f'noncomputable def {F} ({argstr} : V) : V := subst LAct (listToVec [{lst}]) {P}')
            emit(f'lemma isFormula_{F} {binder} {hyps} : IsFormula LAct ({F} {argstr}) :=')
            emit(f'  isFormula_fact isSemiformula_{P} _ rfl {mem_term([f"h{a}" for a in args])}')
        if not (existing and F == 'piFact'):
            emit(f'lemma shift_{F} {binder} {hyps} :')
            emit(f'    shift LAct ({F} {argstr}) = {F} {" ".join(f"(termShift LAct {a})" for a in args)} := by')
            emit(f'  unfold {F}')
            emit(f'  rw [shift_subst_listToVec [{lst}] isSemiformula_{P} shift_{P} (n := 0) {mem_term([f"h{a}" for a in args])}]')
            emit(f'  rfl')
        lhyps = ' '.join(f'(hl{a} : termLen LAct {a} ≤ B)' for a in args)
        emit(f'lemma formulaLen_{F}_le {{B : V}} (hB : 1 ≤ B) {binder} {hyps} {lhyps} :')
        emit(f'    formulaLen LAct ({F} {argstr}) ≤ formulaLen LAct ({P} : V) * B :=')
        emit(f'  formulaLen_fact_le hB isSemiformula_{P} _ rfl {mem_term([f"⟨h{a}, hl{a}⟩" for a in args])}')
        ohyps = ' '.join(f'(ho{a} : fvOcc LAct {a} ≤ M)' for a in args)
        emit(f'lemma fvOccF_{F}_le {{M : V}} {binder} {hyps} {ohyps} :')
        emit(f'    fvOccF LAct ({F} {argstr}) ≤ bvOccF LAct ({P} : V) * M :=')
        emit(f'  fvOccF_fact_le isSemiformula_{P} fvOccF_{P} _ rfl {mem_term([f"⟨h{a}, ho{a}⟩" for a in args])}')
        emit()
    emit('end facts')
    emit()

# ------------------------------------------------------------------ trees
# A piece tree: ('leaf', pred, entries) | ('and', l, r) | ('ex', t)
# entries: list of Lean code strings

def entry_bv(x, env):
    if isinstance(x, tuple):
        if x[0] == 'S':
            return f'bv {env[x[1]]} ^+ (𝟏 : V)'
        if x[0] == 'C':
            return f'cT {x[1]}'
    if x == 'Z':
        return '(𝟎 : V)'
    if x == 'One':
        return '(𝟏 : V)'
    return f'bv {env[x]}'

def entry_inst(x, env, k, wit):
    """entry after instOuterAt k es: bv i (i < k) stays, binder var -> witness"""
    if isinstance(x, tuple):
        if x[0] == 'S':
            return f'{entry_inst(x[1], env, k, wit)} ^+ (𝟏 : V)'
        if x[0] == 'C':
            return f'cT {x[1]}'
    if x == 'Z':
        return '(𝟎 : V)'
    if x == 'One':
        return '(𝟏 : V)'
    if x in wit:
        return wit[x]
    return f'bv {env[x]}'

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
        return f'subst LAct (listToVec [{", ".join(entry_bv(x, env) for x in args)}]) {PREDS[pred][2]}'
    if t[0] == 'and':
        r = code_bv(t[2])
        return f'{code_bv(t[1])} ^⋏ ({r})' if t[2][0] != 'leaf' else f'{code_bv(t[1])} ^⋏ {r}'
    return f'^∃ ({code_bv(t[1])})' if t[1][0] != 'leaf' else f'^∃ {code_bv(t[1])}'

def code_inst(t, k, wit):
    """code after instOuterAt k es pushed to the leaves (k grows under ∃)"""
    if t[0] == 'leaf':
        _, pred, args, env = t
        return f'subst LAct (listToVec [{", ".join(entry_inst(x, env, k, wit) for x in args)}]) {PREDS[pred][2]}'
    if t[0] == 'and':
        r = code_inst(t[2], k, wit)
        return f'{code_inst(t[1], k, wit)} ^⋏ ({r})' if t[2][0] != 'leaf' else f'{code_inst(t[1], k, wit)} ^⋏ {r}'
    return f'^∃ ({code_inst(t[1], k + 1, wit)})'

def semif(t):
    """proof term of IsSemiformula LAct (level) (code t) — level by unification"""
    if t[0] == 'leaf':
        return f'isSemiformula_substRow isSemiformula_{PREDS[t[1]][2]} _ (by rfl) (by row_entries)'
    if t[0] == 'and':
        return f'IsSemiformula.and.mpr ⟨{semif(t[1])}, {semif(t[2])}⟩'
    return f'isSemiformula_exs_cast ({semif(t[1])})'

def semif_inst(t):
    """same, for instantiated pieces: entries are bv's, witnesses (in context), 𝟎, &i, iterated shifts"""
    return semif(t)  # row_entries handles them all

def fact_entry(x, wit):
    if isinstance(x, tuple):
        if x[0] == 'S':
            return f'({fact_entry(x[1], wit)} ^+ (𝟏 : V))'
        if x[0] == 'C':
            return f'(cT {x[1]})'
    if x == 'Z':
        return '(𝟎 : V)'
    if x == 'One':
        return '(𝟏 : V)'
    w = wit[x]
    return w if ' ' not in w else f'({w})'

def fact_code(pred, args, wit):
    return f'{PREDS[pred][3]} {" ".join(fact_entry(x, wit) for x in args)}'

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

# ------------------------------------------------------------------ rows
def gen_row(name, binders, ants, conc):
    m = len(binders)
    env = {v: i for i, v in enumerate(binders)}
    R = f'row_{name}'
    is_ex = conc[0] == 'ex'
    closed = any(isinstance(x, tuple) and x[0] == 'C' for x in (conc[2] if not is_ex else []))
    ant_trees = [tree_of(a_, env) for a_ in ants]
    Pset = set(PREDS[l[1]][2] for t in ant_trees + [tree_of(conc, env)] for l in leaves(t))
    Punfold = ' '.join(sorted(Pset))
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
        nested = conj[-1][0] == 'ex'
        if nested:
            a2 = len(conj[-1][1])
            inner = body
            for _ in range(len(conj) - 1):
                inner = inner[2]
            for _ in range(a2):
                inner = inner[1]
            emit(f'noncomputable def {R}_inner : V := {code_bv(inner)}')
            # body code with inner named
            def code_bv_named(t, depth):
                if depth == 0 and t is body:
                    pass
                return None
            # body = A ⋏ (B ⋏ ∃∃∃ inner): rebuild the code string with the name for the inner conj
            outer = conj[:-1]
            env2 = {k: v + a1 for k, v in env.items()}
            for i, v in enumerate(vs):
                env2[v] = a1 - 1 - i
            parts = [code_bv(tree_of(it, env2)) for it in outer]
            s = '^∃ ' * a2 + f'{R}_inner'
            for c in reversed(parts):
                s = f'{c} ^⋏ ({s})'
            emit(f'noncomputable def {R}_body : V := {s}')
            unf_body = f'{R}_body {R}_inner'
        else:
            emit(f'noncomputable def {R}_body : V := {code_bv(body)}')
            unf_body = f'{R}_body'
        emit(f'noncomputable def {R}_R : V := {"^∃ " * (a1 - 1)}{R}_body')
        emit(f'noncomputable def {R}_c : V := ^∃ {R}_R')
        unf_c = f'{R}_c {R}_R {unf_body}'
    emit()
    # ---- row-shape
    emit(f'theorem quote_row_{name} : (⌜Semiformula.lMap emb {name}B⌝ : V) = impChain LAct {R}_as {R}_c := by')
    if closed:
        p, args = conc[1], conc[2]
        emit(f'  unfold {R}_as {unf_c} {Punfold}')
        emit(f'  rw [show {name}B = {PREDS[p][0]} ⇜ ![{", ".join(f"cTT {x[1]}" for x in args)}] from rfl]')
    else:
        emit(f'  unfold {name}B {R}_as {unf_c} {Punfold}')
    emit(f'  all_goals row_shape')
    emit()
    # ---- formula-ness
    lvl = f'(({m} : ℕ) : V)'
    emit(f'lemma isSemiformula_{name}_as : ∀ A ∈ {R}_as, IsSemiformula LAct {lvl} A := by')
    emit(f'  unfold {R}_as')
    emit(f'  exact {mem_term([semif(t) for t in ant_trees])}')
    emit(f'lemma isSemiformula_{name}_c : IsSemiformula LAct {lvl} {R}_c := by')
    emit(f'  unfold {unf_c}')
    emit(f'  exact {semif(tree_of(conc, env))}')
    if is_ex:
        Rtree = full
        for _ in range(1):
            Rtree = Rtree[1]
        emit(f'lemma isSemiformula_{name}_R : IsSemiformula LAct (({m + 1} : ℕ) : V) {R}_R := by')
        emit(f'  unfold {R}_R {unf_body}')
        emit(f'  exact {semif(Rtree)}')
        emit(f'lemma isSemiformula_{name}_body : IsSemiformula LAct (({m + a1} : ℕ) : V) {R}_body := by')
        emit(f'  unfold {unf_body}')
        emit(f'  exact {semif(body)}')
        emit(f'lemma {R}_R_eq : ({R}_R : V) = exsIter {a1 - 1} {R}_body := rfl')
    emit()
    # ---- instantiation
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
        pieces = dedupe([code_bv(t) + '|' + PREDS[t[1]][2] for t in ant_trees + [tree_of(conc, env)]])
        rws = ', '.join(f'instOuter_subst_listToVec _ isSemiformula_{pc.split("|")[1]} (by rfl) _ hes (by row_entries)' for pc in pieces)
        emit(f'  rw [{rws}]')
        emit(f'  all_goals try row_entries_simp')
        emit(f'  row_finish')
        emit()
        return
    # existential conclusion
    vs, conj = conc[1], conc[2]
    a1 = len(vs)
    nested = conj[-1][0] == 'ex'
    def sh(e, k):
        return f'termShift LAct {e}' if k == 1 else f'(termShift LAct)^[{k}] {e}'
    wit1 = {v: sh(wname(v), a1) for v in binders}
    for i, v in enumerate(vs):
        wit1[v] = f'^&(({a1 - 1 - i} : ℕ) : V)'
    outer_items = conj[:-1] if nested else conj
    emit(f'lemma inst_{name} {binder}{hyps} :')
    emit(f'    {R}_as.map (instOuter LAct {es}) = [{", ".join(ant_facts)}] ∧')
    if not nested:
        rhs = conj_facts(outer_items, wit1)
        emit(f'    freeIter LAct {a1} (instOuterAt LAct {a1} {es} {R}_body) = {rhs} := by')
    else:
        a2 = len(conj[-1][1])
        inner_inst = code_inst(inner, a1 + a2, wit)
        s = '^∃ ' * a2 + f'(freeIterAt {a2} {a1} ({inner_inst}))'
        for it in reversed(outer_items):
            s = f'{fact_code(it[1], it[2], wit1)} ^⋏ ({s})'
        emit(f'    freeIter LAct {a1} (instOuterAt LAct {a1} {es} {R}_body) = {s} ∧')
        wit2 = {v: sh(wname(v), a1 + a2) for v in binders}
        for i, v in enumerate(vs):
            wit2[v] = f'^&(({a1 - 1 - i + a2} : ℕ) : V)'
        for i, v in enumerate(conj[-1][1]):
            wit2[v] = f'^&(({a2 - 1 - i} : ℕ) : V)'
        emit(f'    freeIter LAct {a2} (freeIterAt {a2} {a1} ({inner_inst})) = {conj_facts(conj[-1][2], wit2)} := by')
    emit(f'  have hes : ∀ e ∈ ({es} : List V), IsSemiterm LAct 0 e := {hes_term}')
    emit(f'  unfold {R}_as {unf_body}')
    emit(f'  simp only [List.map_cons, List.map_nil]')
    if ant_trees:
        pieces = dedupe([code_bv(t) + '|' + PREDS[t[1]][2] for t in ant_trees])
        rws = ', '.join(f'instOuter_subst_listToVec _ isSemiformula_{pc.split("|")[1]} (by rfl) _ hes (by row_entries)' for pc in pieces)
        emit(f'  rw [{rws}]')
    emit(f'  refine ⟨by ((try row_entries_simp); row_finish), ?_' + (', ?_' if nested else '') + '⟩')
    # ---- component 2: push instOuterAt a1 to the leaves
    steps = []
    def push_inst(t, k):
        if t[0] == 'and':
            steps.append(f'instOuterAt_and {k} _ ({semif(t[1])}) ({semif(t[2])}) hes')
            push_inst(t[1], k); push_inst(t[2], k)
        elif t[0] == 'ex':
            steps.append(f'instOuterAt_exs {k} _ ({semif(t[1])}) hes')
            push_inst(t[1], k + 1)
    push_inst(body, a1)
    if not nested:
        leaf_rws = dedupe([f'instOuterAt_subst_listToVec {a1} _ isSemiformula_{PREDS[l[1]][2]} (by rfl) _ hes (by row_entries)|{code_bv(l)}'
                           for l in leaves(body)])
        leaf_rws = [x.split('|')[0] for x in leaf_rws]
    else:
        lr = [f'instOuterAt_subst_listToVec {a1} _ isSemiformula_{PREDS[l[1]][2]} (by rfl) _ hes (by row_entries)|{code_bv(l)}'
              for l in [tree_of(it, env2) for it in outer_items]]
        lr += [f'instOuterAt_subst_listToVec {a1 + a2} _ isSemiformula_{PREDS[l[1]][2]} (by rfl) _ hes (by row_entries)|{code_bv(l)}'
               for l in leaves(inner)]
        leaf_rws = [x.split('|')[0] for x in dedupe(lr)]
    emit(f'  · rw [{", ".join(steps + leaf_rws)}]')
    emit(f'    row_entries_simp')
    # now the goal is freeIter a1 (instantiated body) = rhs
    # instantiated trees
    if not nested:
        ibody = body
    steps = []
    def push_free(t, k):
        # t: bv-tree; instantiated code is code_inst(t, k, wit); level for freeIter is a1
        if t[0] == 'and':
            steps.append(f'freeIter_and {a1} ({semif(t[1])}) ({semif(t[2])})')
            push_free(t[1], k); push_free(t[2], k)
        elif t[0] == 'ex':
            pass
    if not nested:
        push_free(body, a1)
        lr = dedupe([f'freeIter_subst_listToVec\' {a1} _ isSemiformula_{PREDS[l[1]][2]} shift_{PREDS[l[1]][2]} (by rfl) (by row_entries)|{code_inst(l, a1, wit)}'
                     for l in leaves(body)])
        lr = [x.split('|')[0] for x in lr]
    else:
        # body = A ⋏ (B ⋏ ∃^a2 inner): freeIter_and per outer node, then freeIter_exs{a2}
        outer_trees = [tree_of(it, env2) for it in outer_items]
        # rebuild the and-chain: A ⋏ (B ⋏ EX)
        exs_tree = inner
        for _ in range(a2):
            exs_tree = ('ex', exs_tree)
        chain = exs_tree
        for ot in reversed(outer_trees):
            chain = ('and', ot, chain)
        def push_free_n(t):
            if t is exs_tree:
                steps.append(f'freeIter_exs{a2} {a1} ({semif(inner)})')
            elif t[0] == 'and':
                steps.append(f'freeIter_and {a1} ({semif(t[1])}) ({semif(t[2])})')
                push_free_n(t[2])
        push_free_n(chain)
        lr = dedupe([f'freeIter_subst_listToVec\' {a1} _ isSemiformula_{PREDS[l[1]][2]} shift_{PREDS[l[1]][2]} (by rfl) (by row_entries)|{code_inst(l, a1, wit)}'
                     for l in outer_trees])
        lr = [x.split('|')[0] for x in lr]
    emit(f'    rw [{", ".join(steps + lr)}]')
    # entry computations
    ent = []
    used_bv = set(); used_w = set()
    lv = leaves(body) if not nested else [tree_of(it, env2) for it in outer_items]
    for l in lv:
        for x in l[2]:
            base = x[1] if isinstance(x, tuple) and x[0] == 'S' else x
            if isinstance(base, tuple) or base in ('Z', 'One'):
                continue
            if base in binders:
                used_w.add(base)
            else:
                used_bv.add(l[3][base])
    for i in sorted(used_bv):
        ent.append(f'freeIterT_bv0 {a1} {i} (by norm_num)')
    for v in sorted(used_w):
        ent.append(f'freeIterT_closed 0 h{wname(v)} {a1}')
    zs = [f'freeIterT_closed 0 (isSemiterm_qqZero_LAct 0) {a1}', f'iterate_termShift_qqZero {a1}'] if any(x == 'Z' for l in lv for x in l[2]) else []
    emit(f'    simp only [List.map_cons, List.map_nil]')
    if ent + zs:
        emit(f'    rw [{", ".join(ent + zs)}]')
    emit(f'    try rfl')
    if nested:
        # ---- component 3
        steps = []
        def push_at(t):
            if t[0] == 'and':
                steps.append(f'freeIterAt_and {a2} {a1} ({semif(t[1])}) ({semif(t[2])})')
                push_at(t[1]); push_at(t[2])
        push_at(inner)
        lr = dedupe([f'freeIterAt_subst_listToVec {a2} {a1} _ isSemiformula_{PREDS[l[1]][2]} shift_{PREDS[l[1]][2]} (by rfl) (by row_entries)|{code_inst(l, a1 + a2, wit)}'
                     for l in leaves(inner)])
        lr = [x.split('|')[0] for x in lr]
        emit(f'  · rw [{", ".join(steps + lr)}]')
        used_lt = set(); used_ge = set(); used_w = set(); hasZ = False
        for l in leaves(inner):
            for x in l[2]:
                base = x[1] if isinstance(x, tuple) and x[0] == 'S' else x
                if isinstance(base, tuple):
                    continue
                if base == 'Z':
                    hasZ = True; continue
                if base == 'One':
                    continue
                if base in binders:
                    used_w.add(base)
                elif base in conj[-1][1]:
                    used_lt.add(l[3][base])
                else:
                    used_ge.add(l[3][base])
        ent = []
        for i in sorted(used_lt):
            ent.append(f'freeIterT_bv_lt {a2} {a1} {i} (by norm_num)')
        for i in sorted(used_ge):
            ent.append(f'freeIterT_bv_ge {a2} {a1} {i} (by norm_num) (by norm_num)')
        for v in sorted(used_w):
            ent.append(f'freeIterT_closed {a2} h{wname(v)} {a1}')
        if hasZ:
            ent.append(f'freeIterT_closed {a2} (isSemiterm_qqZero_LAct 0) {a1}')
        emit(f'    simp only [List.map_cons, List.map_nil]')
        emit(f'    rw [{", ".join(ent)}]')
        emit(f'    try simp only [Nat.reduceSub]')
        # phase 2: freeIter a2 on the result
        steps = []
        def push_free2(t):
            if t[0] == 'and':
                steps.append(f'freeIter_and {a2} ({semif(t[1])}) ({semif(t[2])})')
                push_free2(t[1]); push_free2(t[2])
        push_free2(inner)
        lr = dedupe([f'freeIter_subst_listToVec\' {a2} _ isSemiformula_{PREDS[l[1]][2]} shift_{PREDS[l[1]][2]} (by rfl) (by row_entries)|{l[1]}{l[2]}'
                     for l in leaves(inner)])
        lr = [x.split('|')[0] for x in lr]
        emit(f'    rw [{", ".join(steps + lr)}]')
        ent = []
        for i in sorted(used_lt):
            ent.append(f'freeIterT_bv0 {a2} {i} (by norm_num)')
        for i in sorted(used_ge):
            ent.append(f'freeIterT_closed 0 (t := ^&(({i - a2} : ℕ) : V)) (by simp) {a2}')
        for v in sorted(used_w):
            ent.append(f'freeIterT_closed 0 (isSemiterm_iterate_termShift h{wname(v)} {a1}) {a2}')
        if hasZ:
            ent.append(f'freeIterT_closed 0 (isSemiterm_iterate_termShift (isSemiterm_qqZero_LAct 0) {a1}) {a2}')
        emit(f'    simp only [List.map_cons, List.map_nil]')
        emit(f'    rw [{", ".join(ent)}]')
        emit(f'    try simp only [termShift_iterate_fvar, ← Function.iterate_add_apply, ← Nat.cast_add, Nat.reduceAdd]')
        emit(f'    try rfl')
    emit()

def gen():
    gen_preds()
    emit('/-! ## 3. The rows: pieces, row-shape, formula-ness, instantiation -/')
    emit()
    emit('section rows')
    emit()
    for (name, binders, ants, conc) in ROWS:
        if SUBSET is not None and name not in SUBSET:
            continue
        gen_row(name, binders, ants, conc)
    emit('end rows')
    emit()

gen()
header = open(sys.argv[1] + '.head').read()
open(sys.argv[1], 'w').write(header + '\n'.join(out) + '\nend ArithS\n')
print('rows:', len([r for r in ROWS if SUBSET is None or r[0] in SUBSET]))
