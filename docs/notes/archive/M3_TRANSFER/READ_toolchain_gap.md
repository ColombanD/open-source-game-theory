# TASK C — Toolchain-gap risk map: engine/ Lean v4.28.0 → v4.33.1 (+ Mathlib v4.28.0 → 0df444a360ea = tag v4.33.1)

Method: read-only greps over `engine/PrisonersDilemma/**` (built modules = everything except `Research/`, which is NOT a lake root and is never imported by `PrisonersDilemma.lean`/`Decidability.lean`/`Outcome/Check.lean`); release notes fetched from lean-lang.org (v4.29.0–v4.33.1); LeanInteract README/PyPI; leanprover-community/repl tags; Mathlib docs. No build was run.

## 0. Baseline facts (verbatim)

| Item | Engine (source of truth) | Arith (target) |
|---|---|---|
| `lean-toolchain` | `engine/lean-toolchain:1` `leanprover/lean4:v4.28.0` | `arith/lean-toolchain:1` `leanprover/lean4:v4.33.1` |
| lakefile require | `engine/lakefile.toml:9-12` `[[require]] name = "mathlib" scope = "leanprover-community" rev = "v4.28.0"` | Foundation `rev = "58c76ac8…"`; mathlib inherited `rev 0df444a360eaa60ab8c11dca51a86af692955474`, `inputRev "v4.33.1"` |
| manifest format | `engine/lake-manifest.json:1` `"version": "1.1.0"` (no `fixedToolchain` key) | `arith/lake-manifest.json:1` `"version": "1.2.0"`, trailing `"fixedToolchain": false` |
| vendored mathlib | `engine/.lake/packages/mathlib/lean-toolchain` = `leanprover/lean4:v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (2026-02-16) | mathlib tag `v4.33.1` `lean-toolchain` = `leanprover/lean4:v4.33.1` (verified via raw GitHub) |
| inherited deps pinned by version | `Cli` `inputRev "v4.28.0"`, `proofwidgets` `inputRev "v0.0.87"` (`engine/lake-manifest.json`) | arith manifest adds `doc-gen4`, `leansqlite`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`, `axiom-audit` (Foundation-only; irrelevant to engine) |
| elan | `elan toolchain list` already has `leanprover/lean4:v4.33.1` (and v4.29.0, v4.30.0, v4.31.0, v4.32.2) | — |
| `.lake` location | `engine/.lake/` is a REAL directory inside OneDrive (`build/`, `packages/`); `.gitignore:21` `/engine/.lake/` | `arith/.lake -> /Users/colomband/wt/arith-lake` symlink OUTSIDE OneDrive |
| default targets | `engine/lakefile.toml:7` `defaultTargets = ["PrisonersDilemma", "OutcomeCheck"]`; `Metatheory` (roots `PrisonersDilemma.Decidability`) is UNPINNED from default, build with `lake build Metatheory`; `[[lean_exe]] name = "export_outcomes" root = "PrisonersDilemma.Outcome.Export"` | — |
| CI | `.github/workflows/lean_action_ci.yml:14-16` `uses: leanprover/lean-action@v1` / `lake-package-directory: engine` (reads `engine/lean-toolchain`, no version literal) | — |
| Docs literal | `engine/README.md:186` `**Toolchain:** Lean \`v4.28.0\` (see \`lean-toolchain\`).` | — |
| Worktrees | main tree `colomban-arith-s` @2a16615; `/Users/colomband/wt/osgt-arith-m3` `[colomban-arith-m3]` | — |

Size of the surface: 290 built `.lean` files, 57,329 lines. `Base` 11 files/6,529 lines; `Theorems` 178/19,201; `Decidability` 17/18,894; `Tau` 55/10,146; `Outcome` 5/595; `Bots` 18+8 files/679 lines.

## 1. External-import census (built modules)

Only ONE built file imports Mathlib; everything else gets Mathlib transitively through the `BaseTheorems` umbrella.

| Import line | File:line | Count (built) |
|---|---|---|
| `import Mathlib.Data.Nat.Log` | `Base/Asymptotics.lean:2` | 1 |
| `import Mathlib.Tactic` | `Base/Asymptotics.lean:3` | 1 |
| `import Lean` | `Outcome/Attr.lean:1`, `Outcome/Lint.lean:3`, `Outcome/Export.lean:3`, `Tau/Lint.lean:4` | 4 |
| `import Std.*` / `import Batteries.*` / `import Aesop` / `import Plausible` | — | 0 |

Research-only (NOT built; ignore for the bump): `Mathlib.Data.Nat.Pairing` (8), `Mathlib.Logic.Function.Basic` (8), `Mathlib.Data.Nat.Log` (5) in `Research/Spikes/{pblt,reflection,bounded_lob,transcript}/*.lean`. Root `PrisonersDilemma.lean` has 213 `import` lines, none Mathlib/Std, none Research.

`open` census (built): `open Classical` — `ProofSystem.lean:4`, `Base/Loeb.lean:12`, `Base/AtomCerts.lean:13`, `Base/ValuationSoundness.lean:50`, `Base/Soundness.lean:27`, `Base/Exclusion.lean:91` (+15 `open Classical in`); `open Lean Elab Command Meta` in `Outcome/Lint.lean:28`, `Tau/Lint.lean:17`; NO `open Nat` anywhere (so v4.33 `Nat.ne_of_gt` becoming `protected` is a non-issue: 0 uses of `ne_of_gt`).

Consequence: `Mathlib.Tactic` (whole tactic tree) is in scope for EVERY module, so Mathlib simp-set/normal-form drift reaches all 4,809 `simp` sites, not only Asymptotics.

## 2. Tactic / API census (built modules; occurrences / files)

| Pattern | occ | files | Notes |
|---|---|---|---|
| `omega` | 2054 | 146 | top: T49 206, T31 180, T48 139, Base/Loeb 105, T47 121 |
| `simp` (any) | 4809 | 199 | `simp only` 2426/139; `simp [` 1725/156; `by simp` 676/106 |
| `simpa` | 470 | 122 | **v4.31 #13636 target** |
| `decide` (word) | 541 | 115 | `by decide` 403/98; `decide (` term-level in deciders: T31 129 lines, T44 56, T52 42, T47 8, T49 6, Tau/Vote 5, T53 5 |
| `decide_eq_true_eq` | 154 | — | `Bool.and_eq_true` 360, `Bool.or_eq_true` 40, `List.any_eq_true` 88, `decide_eq_false_iff` 2, `of_decide_eq_true` 8, `Bool.true_or` 129, `Bool.or_true` 80 |
| `rfl` | 1734 | 174 | `:= rfl` 260/40; `by rfl` 78/34 |
| `subst` | 1832 | 144 | `injection` 480/29; `exfalso` 124/54; `absurd` 498/83; `nomatch` 10/3 |
| `obtain` / `rcases` / `rintro` | 1409/329/404 | 136/39/59 | Mathlib `rcases` patterns everywhere |
| `simp_all` | 50 | 13 | `Theorems/{GuardianBot,WaryBot,DIMCID,LegibleBot}/*` inside `all_goals (first | simp [X] at hme | … | simp_all)` combinators; `Theorems/WaryBot/Helpers.lean:512-546`; `Tau/Theorems/TauDIMCID/Helpers.lean:1297` |
| `norm_num` | 13 | 6 | `Base/Asymptotics.lean:48,61,110,113,126,129`, `Theorems/OptimBot/vs_DBot.lean:69,73`, `vs_TitForTatBot.lean:219,222`, `Theorems/PrudentBot/vs_EBot.lean:31`, `vs_MirrorBot.lean:34`, `Base/AtomCerts.lean:85` |
| `linarith` / `nlinarith` | 4 (+3 nlinarith) | 1 | `Base/Asymptotics.lean:46,59,67,84` (uses `sq_nonneg`, `ring`, `pow_add`) |
| `positivity` | 0 real | — | the single hit is prose (`T31EngineDecider.lean:31` section title) |
| `aesop`, `native_decide`, `exact?`, `apply?`, `grind`, `bv_decide`, `cases'`, `induction'` | 0 | — | none |
| `termination_by` / `decreasing_by` | 15 / 7 | 4 / 2 | see §3.8 |
| `deriving` | 9 | 6 | `Program.lean:6` `deriving DecidableEq, Repr, BEq`; **`Program.lean:92` `deriving instance DecidableEq for Prog, VoteList, ProgList, Formula`** (4-way mutual); `Tau/Spec.lean:95,101,122`, `Tau/Roster.lean:86`, `Outcome/Spec.lean:32` `deriving DecidableEq, Repr, Inhabited`, `Outcome/Lint.lean:48`, `Tau/Lint.lean:29` `deriving Repr` |
| `set_option` | 17 | 15 | ALL `maxHeartbeats` except `T31EngineDecider.lean:1643` `set_option linter.unusedSimpArgs false in`; values: 1000000 ×11, 1600000 (`Base/ValuationSoundness.lean:470`), 2000000 (`T48CutRelevance.lean:1030`, `Tau/Theorems/TauCupod/Helpers.lean:24`), 4000000 (`T53StabInst.lean:143`, `T47Stabilization.lean:364`). **`maxRecDepth` is set NOWHERE in engine.** |
| `@[elab_as_elim]` | 2 | 1 | `ProofSystem.lean:541` (`Pf.induct`), `:766` (`PlaysProof.induct`) |
| raw `Pf.rec` | 7 uses | 6 | `ProofSystem.lean:701`, `Base/Transpose.lean:445`, `Base/ValuationSoundness.lean:652`, `T48CutRelevance.lean:443,1036`, `T42PfB.lean:487`, `T31EngineDecider.lean:1648,2210` |
| raw `PlaysProof.rec` | 2 | 2 | `ProofSystem.lean:848`, `Base/ValuationSoundness.lean:524` |
| other raw `.rec` | 10 | 6 | `PfG.rec` `T42PfB.lean:271,407`, `T44BoundedDecider.lean:640`, `T52DecInst.lean:480`, `T51Regress.lean:175` (`T42.PfG.rec`); `PlaysProofG.rec` `T42PfB.lean:341`; `Formula.rec (motive_1 := fun _ => True)` `T53StabInst.lean:48`, `T43ModestUniverse.lean:388,423`, `T47Stabilization.lean:149` |
| `Nat.strong_induction_on` | 8 | 4 | `T49TreeSubstrate.lean:1226,1979,2561,3273,4924`; `Base/ValuationSoundness.lean:518`; `Base/TowerCensus.lean:368`; `Base/Exclusion.lean:511` — all `induction X using Nat.strong_induction_on with | _ X IH => …` |
| `Nat.strongRec*`, `Nat.le_induction` | 0 | — | |
| `List.get?` | 0 (real) | — | all 12 hits are the project's own `ProgList.get?` (`Program.lean:201`) and `ProgList.get?_transpose` (`Base/Transpose.lean:254`) |
| `List.get ` / `Option.get!` / `List.lookup` / `.get?` on List | 0 | — | `.get?` 117 hits are `ProgList.get?`/`defs.get?` |
| `getLast!` / `args[i]!` | 1 / 12 | 3 | `Outcome/Export.lean:32` `(c.module.toString.splitOn ".").getLast!`; `Outcome/Lint.lean:173-206` `args[0]!…args[4]!`, `parts[0]!`; `Tau/Lint.lean:56-65` |
| `String.` API | — | 2 | `Outcome/Lint.lean:240-245` `chunk.takeWhile … .toString`, `(nm.drop 4).toString`, `core.startsWith`, `core.endsWith`, `core.dropRight`, `(core.drop "outcome_".length).toString.splitOn "_vs_"`, `l.all Char.isAlphanum`; `Export.lean:32,87` `splitOn`, `args.head?.getD` |
| `Fin.` | 0 | — | |
| `Nat.sub`/`Nat.sub_le`/`Nat.lt_succ_self`/`Nat.le_of_lt_succ`/`Nat.lt_irrefl` | 1/1/10/0/0 | — | `Nat.sub_le` `Theorems/DIMCID/vs_MirrorBot.lean:131`; `Nat.lt_succ_self` ×10 all in `T49TreeSubstrate.lean` (`ihS F (Nat.lt_succ_self F)`) |
| `List.mem_*` | 339 | 16 | `mem_append` 78, `mem_range` 76, `mem_cons` 55, `mem_append_left` 50, `mem_flatMap` 38, `mem_cons_of_mem` 26, `mem_map` 20, `mem_append_right` 20, `mem_singleton` 16, `mem_cons_self` 13, `mem_filter` 12, `not_mem_nil` 9, `mem_nil_iff` 1 — concentrated in `Decidability/T43,T46,T47,T53` |
| `List.length_*`/`countP_cons`/`map_cons`/`foldr_cons`/`forall_mem_cons` | 2/10/3/2/2 | — | `T47Stabilization.lean:823-855`, `T53StabInst.lean:601-633` |
| `Nat.find`/`Nat.find_spec` | 1/1 | 1 | `T49TreeSubstrate.lean:4662` `(boxInv (Nat.find (boxInv_total t)) t).get (Nat.find_spec (boxInv_total t))` |
| `Prod.Lex` | 15 | 1 | `T49TreeSubstrate.lean:4162-4182` |
| `Classical.byContradiction` | 6 | 2 | `T47Stabilization.lean:913,925,927`, `T53StabInst.lean:691,703,705` |
| `noncomputable` | 4 defs | 2 | `ProofSystem.lean:961` `noncomputable def proofSearch (k : Nat) (φ : Formula) : Bool := decide (Pf k φ)`; `Dynamics.lean:20` `noncomputable def eval : Nat → (me opponent body : Prog) → Option Action`; `:140` `play`; `:143` `outcome` |
| `partial def` | 2 | 2 | `Tau/Lint.lean:32` `partial def listCtors (e : Expr) : MetaM (Array Name)`; `Outcome/Lint.lean:102` `private partial def natText (binder : Name) (e : Expr) (prec : Nat := 0) : MetaM String` |
| `axiom` declarations | 0 | — | all 42 hits are prose |
| `#eval` | 41 | 5 | `T31EngineDecider.lean:3038-3053` (`outcomeG (guardFast 2) 8 …`), `T49TreeSubstrate.lean:1000-4848`, `T50InstanceLob.lean:102-818`, `T54ZooCert.lean:81-285`; Metatheory only |
| `@[simp]` | 42 | 3 | `Base/Transpose.lean:50-402` (25), `Base/Exclusion.lean:109-174` (18), `Tau/Theorems/Helpers.lean:26,29` |
| `initialize` | 3 | 1 | `Outcome/Attr.lean:31,41,47` `registerTagAttribute` |
| Meta API | — | 3 | `whnf` 14 (`Outcome/Lint.lean:146,…`, `Tau/Lint.lean:31-65`), `ppExpr`, `throwError`, `liftTermElabM`, `getEnv`, `realizeGlobalConstNoOverloadWithInfo` (`Lint.lean:310`), `env.find?`, `env.getModuleIdxFor?`, `env.header.moduleNames`, `attr.ext.getState`/`getModuleEntries` (`Attr.lean:63-65`), `importModules`, `initSearchPath (← findSysroot)`, `MetaM.run'`… `.toIO { fileName := "<export>", fileMap := default } { env }` (`Export.lean:92-113`), `Json.mkObj/str/num/arr/bool/null`, `.pretty` |

Mathlib-proper lemma names used in built code (all still present, no `@[deprecated]` in current Mathlib docs — verified for `Nat.strong_induction_on`, `Nat.lt_pow_succ_log_self`, `Nat.pow_log_le_self`, `Nat.log_mono_right`, `Nat.log2_eq_log_two`, `Nat.log_le_self`):
- `Base/Asymptotics.lean:81` `(Nat.le_log2 hk0).mpr hk`; `:83` `rw [Nat.log2_eq_log_two]; exact Nat.pow_log_le_self 2 hk0`; `:96` `exact Nat.log_mono_right h`; `:102` `exact Nat.log_le_self 2 k`; `:110,126` `exact Nat.lt_pow_succ_log_self (by norm_num) k`; `:112,128` `pow_add`; `:115,131` `Nat.one_le_two_pow`; `:117,133` `(Nat.log2_lt (by omega)).2 h3`; `:108,124` `Nat.two_pow_pos _`; `:107,123` `rcases Nat.eq_zero_or_pos k with rfl | hk`; `:45,58` `by ring`; `:59,67` `nlinarith [sq_nonneg m]`.
- Current Mathlib signatures (verbatim from docs): `Nat.lt_pow_succ_log_self {b : ℕ} (hb : 1 < b) (x : ℕ) : x < b ^ (log b x).succ`; `Nat.pow_log_le_self (b : ℕ) {x : ℕ} (hx : x ≠ 0) : b ^ log b x ≤ x`; `Nat.log_mono_right {b n m : ℕ} (h : n ≤ m) : log b n ≤ log b m`; `Nat.log2_eq_log_two {n : ℕ} : n.log2 = log 2 n`; `Nat.log_le_self (b x : ℕ) : log b x ≤ x`; `Nat.strong_induction_on {p : ℕ → Prop} (n : ℕ) (h : ∀ (n : ℕ), (∀ (m : ℕ), m < n → p m) → p n) : p n` — all match the engine's call shapes. (`Nat.strongRecOn'` IS `@[deprecated Nat.strongRec (since := "2026-03-05")]` but the engine does not use it.)
- Same shapes copied in `Theorems/OptimBot/vs_DBot.lean:68-75`, `vs_TitForTatBot.lean:216-224`, `Base/AtomCerts.lean:51-52,85`, `T48CutRelevance.lean:32-38,838,911` (`Nat.lt_two_pow_self (n := M)` — named-arg form), `T49TreeSubstrate.lean:593-596`, `T31EngineDecider.lean:35-37`.

## 3. Release-note changes v4.29.0 → v4.33.1 mapped to engine usage, ranked by blast radius

### R1 — v4.29.0 #12179/#12247/#12567: `isDefEq` no longer bumps transparency to `.default` when comparing implicit arguments ("a very disruptive change"). New `@[implicit_reducible]`; `instance_reducible` renamed `implicit_reducible`.
- Knob: `set_option backward.isDefEq.respectTransparency false`.
- Engine surface: every `exact`/`rw`/`refine`/`simp` unification over `Prog`/`Formula` terms with implicit `{k} {φ}` indices — i.e. the entire 57k lines; the 47-arm `Pf.transpose` (`Base/Transpose.lean:445`) and the `Pf.induct` arm lambdas (`ProofSystem.lean:701-760`, `fun {k} {φ} hatom _ => atom k φ hatom`) unify implicit index arguments that are `.subst`/`.size` applications — exactly the case whose transparency changed. Also `simp only [Prog.transpose, Prog.subst_transpose] at ih ⊢` patterns.
- Expected symptom: `type mismatch` where terms are equal only after unfolding a `def` (`Prog.subst`, `Formula.size`, `numCost`, `c_guard`) inside an implicit argument.

### R2 — v4.31.0 #13636/#13833: `simpa using h` now closes at REDUCIBLE transparency; old behaviour ONLY via per-site `simpa using! h`. No global `backward.*` option (confirmed on PR #13636).
- Engine surface: `simpa` 470 occ / 122 files (e.g. `Base/Transpose.lean:263,567,576,585` `by simpa [Prog.transpose] using ProgList.get?_transpose defs i _ hget`).
- Migration is mechanical sed `simpa using` → `simpa using!` ONLY where it breaks; do not blanket-rewrite (behaviour identical when it already closes at reducible).

### R3 — v4.31.0 #13492/#13363/#13512/#13281/#13280/#13768/#13772: defeq now respects transparency (plain `def` unfolds at `.default`, not at `.reducible` where `simp`/`dsimp` run); #13807 app elaborator beta-reduces args in expected types; #13476 single remaining goal inherits the input goal's tag (`case h =>` after `funext` may rename).
- Knob: `set_option backward.defeqAttrib.useBackward true`, or `@[reducible]`/`@[implicit_reducible]` on the definitions `simp` is expected to see through.
- Engine surface: `simp only [Formula.size, Prog.size, …]` cost arithmetic in every outcome theorem (`Formula.size`/`Prog.size` are plain `def`s in `Program.lean`, `abbrev` count = 36 only); `dsimp only` steps "may need removing". `Outcome/Spec.lean` `OutcomeSpec` and `Tau/RowSpec.lean` `RowSpec` are consumed by `#validate_outcome`/`#check_tau_rows` via `whnf` (not simp) — unaffected.

### R4 — v4.33.0 #13895: `backward.isDefEq.respectTransparency.types` now `true` by default (metavariables assigned at reducible/instances/implicit transparency have their TYPES compared at implicit transparency); #13637 `TransparencyMode.instances` split, `@[implicit_reducible]` loses `@[instance_reducible]` side-effects.
- Knob: `set_option backward.isDefEq.respectTransparency.types false`.
- Surface: same as R1; plus any `simp` lemma whose LHS type is a `def`-wrapped `Prop` (`TailTo`, `TailToS`, `rightTail` simp set `Base/Exclusion.lean:109-174`; `massOf_ifC/ifD` `Tau/Theorems/Helpers.lean:26,29`).

### R5 — v4.33.0 #13956: `maxRecDepth` now bounds KERNEL type-checking deterministically (was physical stack); error `(kernel) deep recursion detected`; 16× headroom; "some existing code depending on deep kernel recursion may need explicit `maxRecDepth` bumps". `decide +kernel` error surfacing improved.
- Engine surface: `by decide` 403/98 files; term-level `decide (…)` deciders `T31EngineDecider.lean` (129), `T44BoundedDecider.lean` (56), `T52DecInst.lean` (42); `T54ZooCert.lean` (37 `decide`, kernel-sealed zoo certificates); `Tau/Theorems/Columns.lean` (18 decide over 494 lines); `:= rfl`/`by rfl` on `Formula.size` numerals (338); every `set_option maxHeartbeats 1000000..4000000` site (§2) is a deep-kernel-term candidate — `T53StabInst.lean:143`, `T47Stabilization.lean:364`, `T48CutRelevance.lean:1030`, `Base/ValuationSoundness.lean:470`, `Tau/Theorems/TauCupod/Helpers.lean:24`, `Decidability/CertifiedOutcomes/{LegibleBot,WaryBot,GuardianBot}.lean`. **No `maxRecDepth` is set anywhere in the engine** — first failure of this kind needs `set_option maxRecDepth N in` at the site (Mathlib tests use 8000).

### R6 — v4.29.0 #12244/#12195: `simp`/`dsimp` no longer process typeclass INSTANCES (`simp +instances` / `set_option backward.dsimp.instances true` restore).
- Grep for `simp [inst…]` hits only project defs named `instOKb`, `instGate`, `instModestP/F` (`T50InstanceLob.lean:179-271`) — NOT instances; false positive. Real exposure: simp sets that relied on unfolding `instDecidableEqAction`/`decEq` to rewrite `decide (a = b)` → the 154 `decide_eq_true_eq` + 360 `Bool.and_eq_true` + 88 `List.any_eq_true` sites (`T47:332`, `T53:110`, `T52:144-254`, `T46:224-239`) if a `Decidable` instance had to be unfolded to reach `decide_eq_true_eq`'s LHS.

### R7 — v4.29.0 #12028: stricter `noncomputable` requirement ("more noncomputable annotations than before may be required"; exemptions: proofs, types, marked functions).
- Surface: consumers of `proofSearch`/`eval`/`play`/`outcome` (all already `noncomputable`, `ProofSystem.lean:961`, `Dynamics.lean:20,140,143`). `Outcome/Spec.lean` `OutcomeSpec … : Prop` (type ⇒ exempt). Any `def … : Bool/Nat/Option` in `Tau/*` or `Theorems/*/Helpers.lean` that mentions `outcome`/`eval` non-propositionally will now error `failed to compile definition, consider marking it as 'noncomputable'` — fix is the annotation.

### R8 — v4.32.0 #13305/#13912: new `do` elaborator is DEFAULT (`set_option backward.do.legacy true` restores); `do` needs `Pure`; `do match` non-dependent by default; `let pat := rhs | otherwise` now scopes over the following doSeq; `return e` inside `(← do …)` early-returns from the ENCLOSING block.
- Surface: `Outcome/Lint.lean` (4 `| throwError` alternatives: `:158 let some ci := env.find? n`, `:173 let some regime := (← whnf args[0]!).constName?`, `:175 let some pad ← natLit? args[1]!`, `:181 let some pair ← resultOf args[4]!`), `Tau/Lint.lean` (5: `:37,44,56,58,94 let some (.inductInfo ind) := env.find? ``PD.Tau.Tmpl`), `Outcome/Export.lean:85-115 main` (nested `let act : MetaM … := do … return (acc, comp)` — `return` is inside a separate `do` VALUE, not `(← do …)`, so unaffected). `Dynamics.lean:143` `outcome … := do` on `Option` (has `Pure`). Expected impact: nil-to-low; the `| throwError` alternative form is exactly what the new scoping was designed for.

### R9 — v4.33.1 #14582: kernel rejects inductives where "a datatype being declared occurs applied to anything other than the parameters and universe levels"; #14808 defensive re-typechecking of generated recursors.
- Surface: `Program.lean:26-91` (4-way mutual, no params), `ProofSystem.lean:161-287` (`PlaysProof : (me opponent body : Prog) → Action → Nat → Prop`, `VoteAllPlay : VoteList → Nat → Prop`, `AtomProvable : Nat → Formula → Prop`, `Pf : Nat → Formula → Prop` — INDEXED, no params ⇒ rule N/A), `T42PfB.lean:78,110,116` (`PlaysProofG (G : Formula → Prop) …`, `PfG (G : Formula → Prop) : Nat → Formula → Prop` — every recursive occurrence sampled is `PfG G …` with the SAME `G` ⇒ uniform ⇒ OK), `T49TreeSubstrate.lean:38-78` `PlaysT/AtomT/ProvT : … → Type`, the six `SP*`/`WaryPrudentCensus (k : Nat) : Prog → Prog → Prop` census inductives (`Theorems/WaryBot/*`, `Theorems/DIMCID/vs_CupodTrollBot.lean:18`), `Base/Closure.lean:229 inductive Deriv (hyp : Formula) : Formula → Prop`. Verify parameters are uniform in `SP*` and `Deriv` bodies (not sampled). Risk low; #14808 only errors if the recursor were ill-typed.

### R10 — v4.29.0 #12514: universe inference — recursive types no longer "obvious Prop candidates"; universe mvars in ctor fields not promoted.
- All inductive heads carry an explicit sort (`: Type where` / `: … → Prop where`, list in §3 grep) EXCEPT `Program.lean:3 inductive Action`, `ProofSystem.lean:104 inductive CtxLayer where`, `:132 inductive SearchLayer2 where`, `Tau/Spec.lean:94,100,117` (`inductive Mode | …`, `inductive Target (ι : Type) | self | name (i : ι)`, `inductive Spec (ι : Type)`), `Outcome/Spec.lean:25 inductive BudgetRegime`, `Tau/Roster.lean:83 inductive Tmpl` — all non-recursive enums/ADTs in `Type`, unaffected (change concerns recursive types being inferred `Prop`; none of these are recursive except `Spec`, which is `Type`-valued by field types).

### R11 — v4.30.0 #12603: constructors starting with TYPELESS binders `(x)` must become `(x : _)`. Grep found none in built modules. #12897 `inferInstanceAs` needs expected type — 0 uses. #13005 `compileDecl` needs `markMeta` — 0 uses. #12749 `isStructureLike`→`isNonRecStructure` — 0 uses.

### R12 — v4.29.0 #12441 String/Subarray → `Std.Slice`; v4.30 String verification of `startsWith/drop/take/split/intercalate`; v4.31 #13155 `String.dropWhile/takeWhile` verified; #13400 `String.Pos.skipWhile_le`→`le_skipWhile`.
- Surface: `Outcome/Lint.lean:240-245` (`chunk.takeWhile fun c => …).toString`, `(nm.drop 4).toString`, `(core.drop "outcome_".length).toString.splitOn "_vs_"`, `core.dropRight suffix.length`, `l.all Char.isAlphanum`) and `Export.lean:32` `(… .splitOn ".").getLast!`. The `.toString` after `drop`/`takeWhile` shows these already return a slice at 4.28; if 4.29–4.33 changed `String.drop : … → String` (round-trip) the `.toString` calls become type errors — trivial to fix, but it is the census gate (`OutcomeCheck` is a DEFAULT target), so it blocks `lake build`.

### R13 — Lake: manifest `"version": "1.1.0"` → `"1.2.0"` with `"fixedToolchain": false` (arith shows the new schema); v4.32 #13893 `lake lint` flags removed; v4.33 #14300 `setup` facet not buildable from CLI; new package options `requiresModuleSystem`/`allowNonModules` (warn-only; engine has no `module` files). `lake update mathlib` rewrites the manifest and drops the `inputRev "v4.28.0"` on `Cli`. Engine uses `lakefile.toml` (no `lakefile.lean`) — no Lake DSL breakage. `.lake/build/lib/lean/<mod>` layout assumed by `app/src/pd_runner/services/bot_profile.py:248-254` — unchanged for non-module packages (4.33 `.ltar` archives are module-system only).

### R14 — Mathlib v4.28.0 → v4.33.1 (5 months): no deprecation found for any name in §2's Mathlib list; `Nat.find`/`Nat.find_spec` used at `T49TreeSubstrate.lean:4662` resolve (core or `Mathlib.Data.Nat.Find`, both reachable via `Mathlib.Tactic`). `nlinarith`/`linarith`/`norm_num`/`ring`/`positivity`-free. Expect only simp-normal-form drift from Mathlib's `@[simp]` set (Mathlib's simp lemmas ARE in scope everywhere because of `import Mathlib.Tactic`) — same symptom class as R3.

### R15 — v4.29 #12217 native computation as one axiom per computation (`#print axioms` shows `._native.…`): engine has 0 `native_decide` — the 3-axiom footprint claim (`Base/BoundedGL.lean:7` `#print axioms` audit) is unaffected.

Not applicable (0 usages): `grind`, `aesop`, `Lean.RBMap` (v4.32 deprecated), `Std.Time`/`DateTime`, `Float.lt/le` Bool change, `UInt8.ofNatTruncate`, `Subarray.*`, `IO.AsyncList`, `Int.Linear`, FFI/`Lean.initializing`, `lia`/`Rat`, `bv_decide`.

## 4. App coupling (exact lines)

- No file in `app/` reads `engine/lean-toolchain`, `lakefile.toml`, or `lake-manifest.json`; the only hard-coded version literal anywhere is `engine/README.md:186`. `grep '4\.28|lean_version|toolchain'` over `app/src`, `app/tests`, `app/pyproject.toml`, `app/uv.lock` → 0 code hits (the two `generated/outcomes/*.json` hits are transcript text).
- `app/pyproject.toml:14` `"lean-interact>=0.11.5",` ; `app/uv.lock:859-875` `name = "lean-interact"` `version = "0.11.5"` (sdist/wheel `upload-time = "2026-07-16T22:43:1x"`), `uv.lock:1246` `{ name = "lean-interact", specifier = ">=0.11.5" }`.
- LeanInteract README (main): **"Supports all Lean versions between `v4.8.0-rc1` and `v4.32.0-rc1`."**; for `LocalProject` it "automatically detects the Lean and REPL versions from the project's `lean-toolchain` file"; "For Lean versions exceeding the maximum supported version (`v4.32.0-rc1`), the system will use the newest available cached REPL version." PyPI latest = 0.11.5 (2026-07-16) — predates Lean v4.33.1 (2026-08-21). `leanprover-community/repl` tags: `v4.33.0` (2026-08-10), `v4.34.0-rc1/rc2` exist; **`v4.33.1` tag → HTTP 404**. ⇒ After the bump, `LocalProject(directory=engine)` will look for REPL `v4.33.1`, not find it, and fall back to a cached REPL built against a different toolchain — expect the `Command(cmd="\n".join(imports))` env load to fail (olean version mismatch) → caught by `interact.py:160-185` and silently degraded to `lake env lean`.
- Call sites: `app/src/pd_runner/lean/interact.py:97` `from lean_interact import AutoLeanServer, LeanREPLConfig, LocalProject`; `:103-105` `config = LeanREPLConfig(project=LocalProject(directory=str(self._engine_dir), auto_build=False))`; `:110-112` `AutoLeanServer(config, max_total_memory=0.95, max_process_memory=None)`; `:128-131` `server.run(Command(cmd=…), timeout=_CHECK_TIMEOUT_S, add_to_session_cache=True)`; `:199` `server.run(Command(cmd=body, env=env), timeout=_CHECK_TIMEOUT_S)`; degrade paths `:165-185` ("Setup failed (download/build/toolchain) — do not retry per call", "LeanInteract failed %d times in a row … disabling"); kill-switch env `PD_LEAN_INTERACT=0` (`settings.py:80-83` comment; CLAUDE.md). `app/tests/test_interact.py:9` imports `lean_interact.interface.CommandResponse` (import-only; no version pin).
- `lake` subprocess users (all version-agnostic CLI): `lean/executor.py:25` `["lake","env","lean",str(lean_file_arg)]`, `:58` `["lake","build",*targets]`; `eval/outcome_prepass.py:249` `["lake","env","lean","-M",str(memory_mb),str(scratch)]` (`-M` still valid), `:300` `["lake","build",*[f"+{m}" for m in modules]]`; `eval/outcome_matrix.py:342-343` `["lake","build","PrisonersDilemma","OutcomeCheck"]`, `["lake","exe","export_outcomes",…]`; `services/library_writer.py:166` builds `PrisonersDilemma + OutcomeCheck`; `services/constructor_integration.py:168,213,359` `lake build <target>` in a git worktree; `services/bot_profile.py:248-254` deletes `.lake/build/lib/lean/PrisonersDilemma/Bots/LlmGenerations/<Bot>.*` and `.lake/build/ir/…` (layout unchanged).
- Prompt-embedded Lean text: `llm/prompts.py`, `llm/lean_index.py::strip_proof_bodies` embed `ProofSystem.lean`/`Base/Exclusion.lean` digests and few-shot theorem files — if the bump rewrites `simpa using` → `simpa using!` or adds `set_option` lines, few-shots change (harmless, but E1 baseline comparability shifts).

## 5. Bump command sequence (worktree, `.lake` outside OneDrive)

```
# 0. worktree + fast disk for .lake (mirror arith: arith/.lake -> ~/wt/arith-lake)
git worktree add ~/wt/osgt-bump -b colomban-toolchain-4.33 main
mkdir -p ~/wt/osgt-bump-lake && ln -s ~/wt/osgt-bump-lake ~/wt/osgt-bump/engine/.lake
# (optional seed) cp -R "<main>/engine/.lake/packages" ~/wt/osgt-bump-lake/   # reuse git clones, NOT build/
cd ~/wt/osgt-bump/engine
# 1. pins
printf 'leanprover/lean4:v4.33.1\n' > lean-toolchain
sed -i '' 's/^rev = "v4.28.0"/rev = "v4.33.1"/' lakefile.toml          # engine/lakefile.toml:12
elan toolchain list | grep v4.33.1                                       # already installed
# 2. manifest + cache (rewrites lake-manifest.json to 1.2.0 + fixedToolchain; mathlib -> 0df444a360ea)
lake update mathlib
grep -n '"rev": "0df444a360eaa60ab8c11dca51a86af692955474"' lake-manifest.json
lake exe cache get                                                       # mathlib oleans for v4.33.1
# 3. layered build, engine first (stop at first red file; fix bottom-up)
lake build +PrisonersDilemma.Program +PrisonersDilemma.ProofSystem +PrisonersDilemma.Dynamics
lake build +PrisonersDilemma.Base.Asymptotics                            # the ONE Mathlib importer
lake build +PrisonersDilemma.Base.Soundness +PrisonersDilemma.Base.ValuationSoundness +PrisonersDilemma.Base.Transpose +PrisonersDilemma.Base.Exclusion +PrisonersDilemma.Base.Loeb +PrisonersDilemma.Base.TowerCensus
lake build PrisonersDilemma                                              # all theorems + tau
lake build OutcomeCheck                                                  # #check_outcome_theorems + #check_tau_rows (Lint/Attr/Meta API)
lake build Metatheory                                                    # T31…T54 (NOT in defaultTargets)
lake exe export_outcomes                                                 # refresh app/generated/outcome_theorems.json + tau_rows.json; expect byte-identical cells
# 4. footprint + demos
grep -rn '#print axioms' PrisonersDilemma | head; lake env lean PrisonersDilemma/Decidability/T31EngineDecider.lean   # #eval demos unchanged
# 5. app
cd ../app && PD_LEAN_INTERACT=0 uv run pytest -q                         # REPL path expected to degrade (no repl v4.33.1 tag)
uv run pytest -q tests/test_interact.py                                  # then without the kill-switch to observe the degrade log
sed -i '' 's/Lean `v4.28.0`/Lean `v4.33.1`/' ../engine/README.md        # engine/README.md:186
```
First-pass compatibility knobs (put in `engine/lakefile.toml` as package-level `leanOptions = { … }` or `set_option … in` per file, then REMOVE one by one): `backward.isDefEq.respectTransparency = false` (R1), `backward.isDefEq.respectTransparency.types = false` (R4), `backward.defeqAttrib.useBackward = true` (R3), `backward.do.legacy = true` (R8, only if Lint/Export break). There is NO knob for R2 (`simpa using!` per site) or R5 (`maxRecDepth` per site).

## 6. Top-15 file hotspots (why)

| # | File (lines) | Why it is likely to break |
|---|---|---|
| 1 | `Decidability/T49TreeSubstrate.lean` (6603; omega 206, simp 818, obtain 176) | 5× `Nat.strong_induction_on` (`:1226,1979,2561,3273,4924`); 6× `termination_by (k, muF ξ, 1)`/`ξ _ _ => (k, muF ξ, 0)`/`core _ => (k, muF core, 0)` + `decreasing_by` (`:4196-4235, 5206-5235`) over `Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))` (`:4162-4182`) — WF-recursion elaboration + R1/R3 defeq; `Nat.find`/`.get` (`:4662`); `#eval` demos; ~10 `ihS F (Nat.lt_succ_self F)`; R5 kernel depth on the extractor. |
| 2 | `Decidability/T31EngineDecider.lean` (3055; omega 180, decide 68, simp 453) | 129 term-level `decide (…)` in `decFull` (R5/R6); raw `Pf.rec` ×2 (`:1648,2210`) with `maxHeartbeats 1000000` + `linter.unusedSimpArgs false`; `#eval outcomeG …` demos `:3038-3053`; `Nat.log2_eq_log_two` rewrites. |
| 3 | `Base/Transpose.lean` (732; simp 139) | `theorem Pf.transpose {k : Nat} {φ : Formula} (h : Pf k φ) : Pf k φ.transpose := Pf.rec (motive_1 := …) (motive_2 := fun _ _ _ => True) (motive_3 := fun k φ _ => AtomProvable k φ.transpose) (motive_4 := fun k φ _ => Pf k φ.transpose) …` 47 positional arms (`:445+`): implicit-index unification (R1/R4), `simpa [Prog.transpose] using` ×4 (R2), 25 `@[simp]` lemmas (R3), 2× `termination_by structural` (`:290,310`). |
| 4 | `ProofSystem.lean` (970) | `@[elab_as_elim] theorem Pf.induct (motive : (k : Nat) → (φ : Formula) → Pf k φ → Prop) … := Pf.rec (motive_1 := fun _ _ _ _ _ _ => True) (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => True) (motive_4 := motive) …` (`:541-760`) and `PlaysProof.induct … := by refine PlaysProof.rec (motive_1 := motive) …` (`:766-860`): recursor motive/arity is stable, but every downstream `induction h using Pf.induct with` depends on elab_as_elim + R1; the 4-way `mutual … inductive Pf : Nat → Formula → Prop` (`:161-287`) hits R9 recursor re-check. |
| 5 | `Base/ValuationSoundness.lean` (1165) | `induction B using Nat.strong_induction_on with | _ B IH =>` (`:518`) wrapping BOTH raw `PlaysProof.rec` (`:524`) and `Pf.rec` (`:652`) with 4 paired motives under `maxHeartbeats 1600000` (`:470`) — R1/R4/R5 stacked. |
| 6 | `Base/Asymptotics.lean` (~135) | The only Mathlib importer: `import Mathlib.Tactic` (`:3`); `linarith`/`nlinarith [sq_nonneg m]`/`ring`/`norm_num`/`pow_add`; `Nat.le_log2`, `Nat.pow_log_le_self 2 hk0`, `Nat.log_mono_right`, `Nat.log_le_self 2 k`, `Nat.lt_pow_succ_log_self (by norm_num) k`, `(Nat.log2_lt (by omega)).2 h3` — everything downstream imports it, so a Mathlib rename here is a total build stop. |
| 7 | `Outcome/Lint.lean` (322) + `Outcome/Attr.lean` (67) + `Tau/Lint.lean` (108) + `Outcome/Export.lean` (115) | Metaprogramming surface (`initialize … ← registerTagAttribute`, `attr.ext.getState/getModuleEntries`, `whnf`, `ppExpr`, `liftTermElabM`, `realizeGlobalConstNoOverloadWithInfo`, `importModules #[{ module := \`PrisonersDilemma }] {}`, `initSearchPath (← findSysroot)`, `MetaM.run'`… `.toIO {fileName…}{env}`, `Json.*`, `IO.FS.writeFile`), String slice API (`:240-245`, R12), 9 `let some … | throwError` (R8); `OutcomeCheck` is a DEFAULT target ⇒ gates the whole build; `export_outcomes` gates the app's matrix. |
| 8 | `Decidability/T48CutRelevance.lean` (1525; omega 139) | raw `Pf.rec` ×2 (`:443` under `maxHeartbeats 1000000`, `:1036` under `2000000`); `Nat.lt_two_pow_self (n := M)` named-arg (`:911`); `LeafPf : Formula → Type` inductive. |
| 9 | `Decidability/T42PfB.lean` (650) | `PfG.rec (motive_1 := fun me oppo body a n _ => PlaysProof me oppo body a n)` (`:271`), `PlaysProofG.rec` (`:341`), `PfG.rec` (`:407`), `Pf.rec` (`:487`) — 4 raw mutual recursors on the gate-parametric mirror (R1/R9). |
| 10 | `Decidability/T44BoundedDecider.lean` (1112) / `T52DecInst.lean` (969) / `T47Stabilization.lean` (1011) / `T53StabInst.lean` (788) | The deciders: 56/42 `decide (…)` (R5/R6), `PfG.rec` at `T44:640` & `T52:480`, `maxHeartbeats 4000000` at `T47:364`/`T53:143`, `Classical.byContradiction`, `List.countP_cons`/`List.length_cons` rewrites, `Formula.rec (motive_1 := fun _ => True)` (`T47:149`, `T53:48`). |
| 11 | `Base/Exclusion.lean` (2028; simp 317) | `Nat.strong_induction_on` (`:511`) under `maxHeartbeats 1000000` (`:447`); 18 `@[simp]` `rightTail_*`/`TailTo_*`/`TailToS_*` lemmas on `def`s (R3/R4). |
| 12 | `Base/TowerCensus.lean` (595) | `Nat.strong_induction_on` (`:368`) under `maxHeartbeats 1000000` (`:341`). |
| 13 | `Tau/Spec.lean` (321) + `Tau/Vote.lean` (480) + `Tau/Theorems/Columns.lean` (494) + `Tau/Theorems/TauDIMCID/Helpers.lean` (1383) | 3× `termination_by structural fuel _ _ => fuel` (`Spec:197,234,262`) on the `inst` compiler (Gate D1 `rfl` byte-identity relies on definitional unfolding → R3); `Columns.lean` 18 `decide` over 17-row tables (R5); `TauDIMCID/Helpers.lean` `Nat.log` 35, `simp_all` at `:1297`, `set`/`let`+`omega` trap already documented at `:83`. |
| 14 | `Program.lean` (~210) | `deriving instance DecidableEq for Prog, VoteList, ProgList, Formula` (`:92`, 4-way mutual handler); 4× `termination_by structural p _ _ => p` / `f _ _ => f` / `p => p` / `f => f` (`:142,151,187,196`); everything else imports it. |
| 15 | `Theorems/{GuardianBot,WaryBot,DIMCID,LegibleBot}/*.lean` (44 `simp_all` in `all_goals (first | simp [X] at hme | … | simp_all)`) + `Theorems/OptimBot/vs_DBot.lean:68-75`, `vs_TitForTatBot.lean:216-224` (Mathlib `Nat.log` lemma copies) | Combinator chains mask which alternative fires — a simp-normal-form change (R3/R6/R14) flips silently to `simp_all` and may loop/time out; the OptimBot files duplicate Asymptotics' Mathlib calls verbatim. |

## 7. Risk-ranked checklist

1. **[HIGH, global] R1+R4 transparency defaults (v4.29 `isDefEq` implicit args; v4.33 `.types`)** — first build with `backward.isDefEq.respectTransparency=false` and `….types=false`, then remove; triage failures in `Base/Transpose.lean:445`, `ProofSystem.lean:701/848`, `Base/ValuationSoundness.lean:524/652`.
2. **[HIGH, 470 sites] R2 `simpa using` → reducible closing** — no global knob; patch to `simpa using! h` only where red (start `Base/Transpose.lean:263,567,576,585`).
3. **[HIGH, kernel] R5 `maxRecDepth` bounds the kernel** — watch for `(kernel) deep recursion detected` in `T31/T44/T52` deciders, `T54ZooCert.lean` (37 `decide`), `Tau/Theorems/Columns.lean`, every `maxHeartbeats` site; add `set_option maxRecDepth N in` per site (engine currently sets none).
4. **[HIGH, gate] R12/R8 metaprogramming files** — `Outcome/Lint.lean:240-245` String slice API, `Export.lean:32 getLast!`, `Attr.lean` `registerTagAttribute`/`getModuleEntries`, `Export.lean:92-113` `importModules`/`initSearchPath`/`MetaM.run'`…`.toIO`; `OutcomeCheck` is a default target and `export_outcomes` feeds the app — a break here blocks `lake build` AND the matrix even if all theorems compile.
5. **[MED-HIGH, 57k lines] R3 defeq discipline + Mathlib simp-set drift (R14)** — `simp only [Formula.size, …]; omega` cost arithmetic; `dsimp only` steps to delete; 18+25 `@[simp]` lemmas on `def`s in `Base/Exclusion.lean`, `Base/Transpose.lean`; `all_goals (first | … | simp_all)` chains in `Theorems/{GuardianBot,WaryBot,DIMCID,LegibleBot}`.
6. **[MED] R6 simp no longer unfolds instances** — `decide_eq_true_eq`(154)/`Bool.and_eq_true`(360)/`List.any_eq_true`(88) simp sets in `T46/T47/T52/T53`; fix with `simp +instances` or `decide`-instance lemmas.
7. **[MED] WF/structural recursion elaboration** — `T49TreeSubstrate.lean:4196-4235,5206-5235` (`Prod.Lex` triple lex measure + `decreasing_by`), `Program.lean:142-196`, `Tau/Spec.lean:197-262`, `Base/Transpose.lean:290,310` (`termination_by structural`); Gate D1 byte-identity (`inst` compiled terms `rfl`) depends on definitional unfolding surviving R3.
8. **[MED] R7 stricter `noncomputable`** — any non-`Prop` def touching `outcome`/`eval`/`play`/`proofSearch` outside `Dynamics.lean:20-143`/`ProofSystem.lean:961`; mechanical fix.
9. **[MED] App REPL path** — LeanInteract 0.11.5 supports ≤ `v4.32.0-rc1`; `leanprover-community/repl` has `v4.33.0` but NO `v4.33.1` tag → `LocalProject` toolchain detection fails/falls back to a cached REPL; expect silent degrade to `lake env lean` via `interact.py:165-185` (≈20× slower per check, `settings.py:83`); run the app with `PD_LEAN_INTERACT=0` until a `v4.33.1` REPL tag or a LeanInteract release ≥ v4.33 exists (`pyproject.toml:14` / `uv.lock:859-875`), or pin engine to `v4.33.0` instead (repl tag exists) if REPL speed matters more than the 4.33.1 kernel soundness fixes (#14806/#14807/#14843).
10. **[LOW-MED] `deriving instance DecidableEq for Prog, VoteList, ProgList, Formula` (`Program.lean:92`)** — 4-way mutual deriving handler; no documented change v4.29–v4.33 but the handler is version-sensitive; first module to compile, so failure is immediate and cheap to diagnose.
11. **[LOW] R9 v4.33.1 #14582/#14808 kernel inductive/recursor checks** — verify parameter uniformity in `Base/Closure.lean:229 Deriv (hyp : Formula)`, the `SP*`/`WaryPrudentCensus (k : Nat)` census inductives (`Theorems/WaryBot/Helpers.lean:446,587`, `vs_PrudentBot.lean:18`, `vs_DupocBot.lean:28`, `vs_JustBot.lean:124`, `Theorems/DIMCID/vs_CupodTrollBot.lean:18`), `T42PfB.lean:78-116 PfG (G : Formula → Prop)` (sampled uniform).
12. **[LOW] Mathlib name stability** — every used `Nat.log*`/`Nat.strong_induction_on` name verified present and undeprecated in current Mathlib docs; `Nat.strongRecOn'` is deprecated (2026-03-05) but unused; `Nat.lt_two_pow_self (n := M)` (`T48:911`) named-arg form assumes implicit `{n}` — confirm at 4.33 core.
13. **[LOW] Lake/manifest** — `lake update mathlib` rewrites `lake-manifest.json` to `"version": "1.2.0"` + `"fixedToolchain": false` and re-pins inherited packages (`Cli` `inputRev` follows mathlib); commit the rewritten manifest; `.lake/build/lib/lean/...` layout assumed by `app/…/bot_profile.py:248-254` unchanged (no `module` files ⇒ no `.ltar`).
14. **[LOW] OneDrive** — `engine/.lake/` is a real dir inside OneDrive (`build/`+`packages/`, `.gitignore:21`); a full rebuild on 4.33.1 (Mathlib cache + 57k lines + Metatheory) under OneDrive will stall ("Replaying X… time expired (60)"); mirror `arith/.lake -> ~/wt/arith-lake` for the bump worktree.
15. **[LOW] Post-bump acceptance gates** — `lake build PrisonersDilemma OutcomeCheck Metatheory` all green; `lake exe export_outcomes` produces byte-identical `app/generated/outcome_theorems.json`/`tau_rows.json` (`source_digest` check in `outcome_matrix.py:161-207`); `#print axioms` footprint stays at Lean's 3 standard axioms (R15: 0 `native_decide`); `#eval` demos in `T31EngineDecider.lean:3038-3053`, `T54ZooCert.lean` unchanged; `engine/README.md:186` updated; CI `lean_action_ci.yml` picks up `engine/lean-toolchain` automatically.