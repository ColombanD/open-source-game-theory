"""Prompt templates for the proof-search and bot-writer agents."""

from __future__ import annotations

from pd_runner.lean.templates import _ENGINE_PD_DIR


def _read_lean(relative: str) -> str:
    return (_ENGINE_PD_DIR / relative).read_text(encoding="utf-8")


def _bot_uses_search(bot: str) -> bool:
    """True if the bot's source references the `.search` constructor.

    Used to decide whether to inject the proof-system modules (ProofSystem.lean,
    Base/Asymptotics.lean, Base/Loeb.lean, Base/Exclusion.lean) into the proof
    agent's system prompt.
    Reads from `Bots/<bot>.lean` or `Bots/LlmGenerations/<bot>.lean`; missing bot → False.
    """
    for candidate in (f"Bots/{bot}.lean", f"Bots/LlmGenerations/{bot}.lean"):
        try:
            src = _read_lean(candidate)
        except OSError:
            continue
        return ".search" in src or "Prog.search" in src
    return False


def _llm_lemmas_block(exclude_bots: frozenset[str]) -> str:
    """The agent's own derived-rule library, embedded so lemmas added in earlier runs are
    RETRIEVABLE in later ones. In eval mode (`exclude_bots` set), agent-added blocks that
    mention a bot under evaluation are dropped (leak prevention); the delimiters written
    by `add_base_lemma` (`/-! ### <name> (agent-added) -/`) are the split points."""
    try:
        src = _read_lean("Theorems/LlmGenerations/LlmLemmas.lean")
    except OSError:
        return ""
    if exclude_bots:
        lowered = {b.lower() for b in exclude_bots}
        parts = src.split("/-! ###")
        kept = [parts[0]] + [
            blk for blk in parts[1:] if not any(b in blk.lower() for b in lowered)
        ]
        src = "/-! ###".join(kept)
    return (
        "\n\n-- Theorems/LlmGenerations/LlmLemmas.lean (YOUR derived-rule library — lemmas "
        "you or earlier runs added via add_base_lemma; import "
        "`PrisonersDilemma.Theorems.LlmGenerations.LlmLemmas` and use them as "
        "`PD.LlmLemmas.<name>`)\n```lean\n" + src + "\n```"
    )


def _pending_proposals_block() -> str:
    """A short listing of already-filed constructor proposals, so later runs do not
    re-derive and re-file duplicates. Production-mode only (the caller gates it).
    Integrated proposals are skipped here (they are live rules now) and surfaced by
    `_integrated_proposals_block` instead."""
    import json

    from pd_runner.config import load_paths

    root = load_paths().generated_lean_dir.parent / "constructor_proposals"
    if not root.exists():
        return ""
    lines = []
    for meta in sorted(root.glob("*/meta.json")):
        try:
            data = json.loads(meta.read_text(encoding="utf-8"))
            if data.get("status") == "integrated":
                continue
            lines.append(f"- `{data['name']}` — unblocks: {data.get('unblocks', '?')}")
        except (OSError, json.JSONDecodeError, KeyError):
            continue
    if not lines:
        return ""
    return (
        "\n\n# Pending constructor proposals (awaiting human review — do NOT re-file these; "
        "if one of them is exactly what your proof needs, conclude "
        "`OUTCOME OPEN — CONSTRUCTOR PROPOSED <name>` referencing it)\n" + "\n".join(lines)
    )


def _integrated_proposals_block() -> str:
    """Conditional outcome proofs of INTEGRATED constructor proposals.

    Once a proposed rule has been integrated, its constructor is live in
    `ProofSystem.lean` (already embedded in the prompt for `.search` matchups) and
    the bundle's `unblocked_proof.lean` — written with the rule as an explicit
    hypothesis — becomes a near-finished proof: discharge the hypothesis with the
    real constructor and the outcome theorem lands. Surface those proofs so the
    Stage-E proof run starts from them instead of from scratch."""
    import json

    from pd_runner.config import load_paths

    root = load_paths().generated_lean_dir.parent / "constructor_proposals"
    if not root.exists():
        return ""
    parts = []
    for meta in sorted(root.glob("*/meta.json")):
        try:
            data = json.loads(meta.read_text(encoding="utf-8"))
            if data.get("status") != "integrated":
                continue
            proof = meta.parent / "unblocked_proof.lean"
            if not proof.exists():
                continue
            parts.append(
                f"## `{data['name']}` (now a live `Pf` constructor)\n\n"
                f"```lean\n{proof.read_text(encoding='utf-8')}\n```"
            )
        except (OSError, json.JSONDecodeError, KeyError):
            continue
    if not parts:
        return ""
    return (
        "\n\n# Integrated constructors — conditional proofs to discharge\n\n"
        "The following rules were proposed by an earlier run, human-accepted, and are "
        "NOW LIVE constructors in `Pf`. Each block below is a COMPILED outcome proof "
        "written with the rule as an explicit hypothesis. If your target theorem "
        "matches one, adapt it: drop the hypothesis parameter and use the real "
        "constructor (`Pf.<name> ...`) where the hypothesis was applied. This should "
        "need only minor edits — verify with run_lean_proof as usual.\n\n"
        + "\n\n".join(parts)
    )


def build_system_prompt(
    left_bot: str, right_bot: str, exclude_bots: frozenset[str] = frozenset()
) -> str:
    program_src = _read_lean("Program.lean")
    dynamics_src = _read_lean("Dynamics.lean")

    # The `Base/` layer holds the load-bearing proof vocabulary (`proofSearch_spec`,
    # `Pf_sound`, `atom_complete_searchfree`, …) that outcome proofs reference. Since the
    # 2026-07-09 split, `BaseTheorems.lean` is only a re-exporting UMBRELLA (16 lines), so
    # embed the split modules themselves: soundness + atom certificates for every proof.
    # Files are read WITHOUT a fallback: a missing module is a bug (the old silent
    # `except OSError: continue` hid the `SizeLemmas.lean` → `Base/Asymptotics.lean`
    # rename for days).
    proof_blocks = []
    for relative, label in (
        ("BaseTheorems.lean", "BaseTheorems.lean (umbrella — all names live in `PD.BaseTheorems`)"),
        ("Base/Soundness.lean", "Base/Soundness.lean (`proofSearch_spec`, `Pf_sound`, eval monotonicity)"),
        ("Base/AtomCerts.lean", "Base/AtomCerts.lean (constructive atom certificates)"),
        ("Base/Helpers.lean", "Base/Helpers.lean (outcome assembly: `outcome_of_plays`, "
         "`play_ite_from_guard`, `eval_sim_opp_bot_of_play`)"),
    ):
        proof_blocks.append(f"-- {label}\n```lean\n{_read_lean(relative)}\n```")

    # `.search` bots additionally need the proof system itself plus the census/floor
    # exclusion lemmas, the bounded-Löb engines, and the budget (log₂) arithmetic used
    # to discharge `□`/`search` side-conditions. (`Axioms.lean` is gone — the engine has
    # ZERO project axioms since 2026-07-03 and the file itself was later deleted.)
    needs_axioms = _bot_uses_search(left_bot) or _bot_uses_search(right_bot)
    if needs_axioms:
        for relative, label in (
            ("ProofSystem.lean", "ProofSystem.lean (the explicit proof-system `S`)"),
            ("Base/Asymptotics.lean", "Base/Asymptotics.lean (character-budget / log₂ lemmas)"),
            ("Base/Loeb.lean", "Base/Loeb.lean (the bounded-Löb / PBLT engines)"),
            ("Base/Exclusion.lean", "Base/Exclusion.lean (the census + floor exclusion lemmas)"),
            ("Base/Closure.lean", "Base/Closure.lean (closure certificates: telescope subsumption, "
             "sim-composition, SKK=I, the ADMISSIBLE deduction theorem `Deriv`/`deduction_theorem`)"),
        ):
            proof_blocks.append(f"-- {label}\n```lean\n{_read_lean(relative)}\n```")

    proof_system_block = "\n\n" + "\n\n".join(proof_blocks)
    proof_system_block += _llm_lemmas_block(exclude_bots)
    if not exclude_bots:
        proof_system_block += _pending_proposals_block()
        proof_system_block += _integrated_proposals_block()

    return f"""\
You are an expert Lean 4 proof assistant for the open-source game theory project.

# Library definitions

These are the exact source files that define the types, evaluator, and proof rules you must use.
Do not invent definitions — use only what is shown here and imported in the existing theorem files.

-- Program.lean
```lean
{program_src}
```

-- Dynamics.lean
```lean
{dynamics_src}
```{proof_system_block}

# Your task

Write a complete, compilable Lean 4 theorem file that proves the requested outcome theorem.
Use the `run_lean_proof` tool to check your proof. Read errors carefully and fix them.
Use the `read_library_file` tool to inspect existing bot definitions or existing proofs for guidance.

# Rules
- The file must compile with zero errors and zero warnings in stderr.
- Import only modules that exist in the PrisonersDilemma library.
- **Minimal imports.** Import only modules whose definitions or lemmas your file actually
  uses: the two bot modules, the helper/theorem modules you cite by name, and the core
  modules you need. Do NOT copy the import block of an example proof wholesale — the
  few-shot examples may import more than your proof needs, and unused imports accumulate
  as dead weight in the library (Lean emits no warning for them).
- The namespace must be `PD.Theorems`.
- **Every declaration name must be UNIQUE across the whole library.** Your file shares
  the `PD.Theorems` namespace with every existing theorem module, so a helper lemma
  named like an existing one (e.g. `no_provable_OBot_D_tail`, which already exists for
  the CupodBot pair) compiles standalone but breaks the library build with
  `environment already contains ...`. Give EVERY auxiliary lemma a matchup-specific
  name (e.g. `dimcid_obot_no_provable_forbidden`); only the final theorem uses the
  `llm_outcome_<Left>_vs_<Right>` name. `run_lean_proof` appends a WARNING listing any
  collisions — you MUST resolve those warnings before declaring PROOF COMPLETE.
- **Do NOT redefine bots in your proof file.** Every bot already lives in its own
  module under `PrisonersDilemma.Bots.*` — import it (e.g. `import PrisonersDilemma.Bots.CupodBot`)
  and reference it by name. The proof file must contain only theorems, no `def` of any bot.
  Redefining a bot causes a namespace clash at `lake build` time.
- Do not use `sorry`, `admit`, or `native_decide`.
- Prefer `unfold`, `simp`, `rfl`, `exact`, `rw`, `cases`, `omega` tactics.
- **Strict theorem shape — no extra premises.** The theorem's conclusion must be of the form
  `outcome <fuel-expr> <bot_a> <bot_b> = some (.X, .Y)`, optionally wrapped in `∃` / `∀`
  quantifiers over fuel/search-budget naturals (e.g. `∃ k, ∀ n, outcome (n+f) ...` or
  `∃ k₂, ∀ k, k₂ < k → ∃ fuel, ...`). You may NOT add hypotheses of the form
  `proofSearch _ _ = false`, `proofSearch _ _ = true`, or any other premise that conditions
  the outcome on the behavior of the proof oracle. Such hypotheses turn an outcome theorem
  into a conditional claim and defeat the purpose of mechanizing the outcome. Binding the
  search budget `k` with a `∃ k₂, ∀ k, k₂ < k → …` *threshold quantifier* is NOT an extra
  premise — it is the correct way to state the outcome of a `.search`-bot matchup.
- **`.search`-bot matchups depend on the budget `k` — bind it, do not give up.** When one or
  both bots take a budget parameter `k`, the outcome typically flips with `k`: small `k` gives
  defection (the oracle proves nothing), large `k` gives the Löb/Critch cooperation fixed
  point. The unquantified statement with `k` left free is unprovable, but the **large-`k`
  threshold** statement `∃ k₂, ∀ k, k₂ < k → ∃ fuel, outcome fuel (BotA k) (BotB k) = some (…)`
  is provable and is the expected answer. Existing `.search`-bot self-play theorems in the
  few-shot files show the canonical `PBLT` application for this shape — follow it. Prove the
  threshold theorem; do NOT declare OUTCOME OPEN merely because the result varies with `k`.
  Not every self-play matchup cooperates, though: when the Löb premise is NOT derivable at
  the same budget, the honest outcome is determined DEFECTION — the library precedent is
  `outcome_PrudentBot_vs_PrudentBot = (D, D)` (same-`k` single-tier prudence is
  self-defeating), proved via the exclusion census, not declared OPEN.
- **Before ever declaring OUTCOME OPEN, climb the escalation ladder.** Historically, most
  "unprovable" outcomes were provable — the missing piece was a DERIVED rule nobody had
  stated yet (`boxInternalize` and `box_provable` were both once believed to need new
  axioms; both turned out derivable). The ladder:
    1. **Search harder with existing rules** — re-read the Base/ modules in your prompt and
       the few-shot proofs. The rule inventory is COMPLETE for broad fragments since the
       2026-07-28 family-completion program: the positive implicational fragment has its
       full Hilbert basis (`implRefl`, `implK`, `implS` as object formulas — a tautology
       guard like `A → A` is a ONE-LINE `Pf.implRefl`, and the deduction theorem is
       ADMISSIBLE via `Base/Closure.deduction_theorem`); source transparency reads search
       telescopes and mixed search/ite-probe stacks at EVERY depth (`searchChain`,
       `ctxChain` — the old fused rules are certified instances); `.sim`/`.bot` nestings
       compose via `read_compose`/`simStep_compose`; and the modal tier
       (`boxIntro`/`axK`/`box4`/`boxMono`/`impS2`) plus `mutual_loeb`/`pblt_engine_id`
       compose further than it first appears.
    2. **Derive the missing principle as a lemma** (`add_base_lemma`, when available): state
       the reusable rule you wish existed and PROVE it from existing rules. This is always
       safe (kernel-checked, auto-rollback) and the lemma persists for future proofs.
       This rung includes the NEGATIVE direction: "the guard is unprovable" is itself a
       lemma obligation, not a prose claim. Do NOT hand-roll a `Pf.induct` census (the
       proof system has ~30 constructors — a hand-rolled induction is a many-iteration
       trap): instantiate the SHARED kernels in `Base/Exclusion.lean` —
       `no_provable_tailTo_unreadable` (Gödelian targets: certificates impossible at
       every budget + unreadable player), `no_provable_probeFirst_tail` /
       `no_provable_searcherPlay_tail` (the `search_f` floor), or the set-valued
       `no_provable_tailToS_floor` when the target player decomposes as a mixed
       telescope. Each instance is a `refine` plus small shape bullets (the existing
       census instances in the Theorems/ few-shots show the pattern, including the
       `hctx`/`hpthen` mixed-telescope disequalities). A proven `¬ Pf k guard` yields a
       determined else-branch outcome theorem, not OUTCOME OPEN. PLACEMENT: your census
       instance lives in YOUR proof file, with a matchup-specific name — never re-derive
       an instance that already exists in the library (import its module and cite it;
       the few-shots and `read_library_file` show what exists). The kernels stay in
       `Base/Exclusion.lean` — you never write there; when the engine gains a
       constructor, the kernels are repaired centrally and kernel-INSTANCES survive
       untouched (or gain one mechanical bullet), which is exactly why you must
       instantiate kernels instead of hand-rolling inductions.
    3. **Only if derivation genuinely fails**, and you can articulate WHY (which census/
       exclusion argument blocks it, or which Löb/self-reference shape no existing rule
       reads), file a constructor proposal (`propose_pf_constructor`, when available). You
       must supply a COMPILING soundness certificate (the rule's interp-level content proved
       in the current engine) and a faithfulness rationale; the engine is not modified and a
       human reviews the proposal. Also submit `unblocked_proof_lean`: the outcome proof
       with your proposed rule stated as an explicit hypothesis — this kernel-checks your
       "unblocks" claim and preserves the finished proof for the integrator (do the
       verification anyway; submitting it costs nothing extra). Then conclude
       `OUTCOME OPEN — CONSTRUCTOR PROPOSED <name>`.
- **OUTCOME OPEN without a proposal is only for genuinely undetermined matchups, and it
  requires a machine artifact, not prose.** Reserve it for the rare case where *no* single
  action pair holds even past a threshold on `k` (e.g. the matchup admits two incompatible
  fixed points and neither is forced for all sufficiently large `k` — a BISTABLE matchup,
  like a guard naming a frozen `.bot` literal; no sound rule can force those, so do NOT
  propose a constructor for them). Before you may declare bare OUTCOME OPEN you must have
  BOTH (a) attempted the unprovability lemma of rung 2 and be able to point at which
  induction arm genuinely fails, AND (b) explained why no sound-and-faithful rule could
  force either outcome — if such a rule exists, rung 3 (a constructor proposal) is the
  required exit, not OPEN. Beware the false-bistability trap: "both action pairs are
  consistent with `Pf`" is true of EVERY search matchup before you determine which side
  `S` picks — it is not bistability. In particular a guard whose `interp` is TRUE is NEVER
  bistable: either its unprovability is provable by structural exclusion (→ determined
  defection theorem), or the missing capability is a faithful rule a PA-like `S` would
  have (→ constructor proposal). Historical precedent: the tautology guard `A → A` was
  exactly such a case — filed as the `identImpl` proposal, integrated as `Pf.implRefl`
  (2026-07-28), and its blocked outcome became provable. Check the live
  `ProofSystem.lean` in your prompt before assuming a rule is missing.
  When OUTCOME OPEN genuinely applies, do not emit a ```lean``` code block and say exactly
  `OUTCOME OPEN` followed by a one-paragraph explanation of which action pairs are
  consistent with the proof system, why no single pair is forced even in the large-`k`
  limit, and why (a) and (b) both fail.
- When you are confident the proof compiles cleanly, output the final Lean source inside
  a ```lean ... ``` code fence and say "PROOF COMPLETE".
"""


def proof_request_message(
    left_bot: str,
    right_bot: str,
    left_action: str | None,
    right_action: str | None,
    few_shot_files: list[tuple[str, str]],
    known_theorems_summary: str,
    fuel: int | None = None,
) -> str:
    parts: list[str] = []

    # A bot that uses `.search` takes a budget parameter `k` (project convention).
    # When either side is such a bot, the outcome can *flip with `k`* (small `k`:
    # the proof oracle proves nothing, bots defect; large `k`: the Löb/Critch
    # fixed point makes them cooperate). An unquantified `outcome … BotA BotB`
    # statement then leaves `k` free and is genuinely unprovable. The right shape
    # is a **large-`k` threshold theorem** binding `k` — exactly the form used by
    # `outcome_DupocBot_vs_DupocBot`. Detect that case and render the threshold template.
    parameterized = _bot_uses_search(left_bot) or _bot_uses_search(right_bot)

    outcome_clause = (
        f"some (.{left_action}, .{right_action})"
        if left_action is not None and right_action is not None
        else "some (.<LEFT>, .<RIGHT>)"
    )

    if parameterized:
        left_app = f"({left_bot} k)" if _bot_uses_search(left_bot) else left_bot
        right_app = f"({right_bot} k)" if _bot_uses_search(right_bot) else right_bot

        if left_action is not None and right_action is not None:
            intro = (
                "Prove the following outcome theorem. This matchup involves a "
                "`.search` bot, so the outcome depends on the search budget `k`; "
                "state it as a large-`k` threshold theorem:"
            )
        else:
            intro = (
                f"Determine the outcome of `{left_bot}` vs `{right_bot}` and prove it.\n\n"
                f"At least one side is a `.search` bot, so the outcome may depend on the "
                f"search budget `k` (small `k`: the proof oracle proves nothing and the "
                f"bots tend to defect; large `k`: the Löb/Critch fixed point can make them "
                f"cooperate). Prove the **large-`k`** outcome as a threshold theorem of the "
                f"form below, picking the action pair that holds for all sufficiently large "
                f"`k`.\n\n"
                f"The outcome is one of: `(.C, .C)`, `(.C, .D)`, `(.D, .C)`, `(.D, .D)`."
            )

        # Point at the canonical worked example, but not when DupocBot self-play is
        # itself the target (that would name the answer theorem and leak it past the
        # eval harness's `exclude_bots` filter).
        if {left_bot, right_bot} == {"DupocBot"}:
            template_hint = (
                "This is the canonical threshold shape for a `.search`-bot matchup; the "
                "few-shot files show the `PBLT` application that discharges it."
            )
        else:
            template_hint = (
                "This threshold shape is exactly how `outcome_DupocBot_vs_DupocBot` is stated — read "
                "that theorem (and the `PBLT` application it uses) as your template."
            )

        parts.append(
            f"{intro}\n\n"
            f"```lean\n"
            f"theorem llm_outcome_{left_bot}_vs_{right_bot} :\n"
            f"    ∃ k₂, ∀ k, k₂ < k →\n"
            f"      ∃ fuel, outcome fuel {left_app} {right_app} = {outcome_clause} := by\n"
            f"  sorry  -- replace with a real proof\n"
            f"```\n\n"
            f"{template_hint} Do NOT emit an unquantified `outcome … = some (…)` with `k` "
            f"left free; that statement is unprovable because the outcome flips with `k`.\n\n"
            f"Important: name your theorem exactly `llm_outcome_{left_bot}_vs_{right_bot}` "
            f"to avoid clashing with existing library theorems."
        )
    else:
        fuel_expr = f"n+{fuel}" if fuel is not None else "n+<FUEL>"
        fuel_note = (
            f"Use fuel offset `+{fuel}` exactly."
            if fuel is not None
            else (
                "Pick `<FUEL>` yourself: it must be a concrete `Nat` literal large enough that "
                "`outcome (n+<FUEL>) ...` settles to a single action pair for all `n`. Try a small "
                "value first (1 or 3), increase if Lean rejects the proof because evaluation needs "
                "more fuel."
            )
        )

        if left_action is not None and right_action is not None:
            intro = "Prove the following outcome theorem:"
        else:
            intro = (
                f"Determine the outcome of `{left_bot}` vs `{right_bot}` and prove it.\n\n"
                f"The outcome is one of: `(.C, .C)`, `(.C, .D)`, `(.D, .C)`, `(.D, .D)`.\n"
                f"Read the bot definitions, reason about what action each bot plays, "
                f"then write and verify a theorem of the form:"
            )

        parts.append(
            f"{intro}\n\n"
            f"```lean\n"
            f"theorem llm_outcome_{left_bot}_vs_{right_bot} (n : Nat) :\n"
            f"    outcome ({fuel_expr}) {left_bot} {right_bot} = {outcome_clause} := by\n"
            f"  sorry  -- replace with a real proof\n"
            f"```\n\n"
            f"{fuel_note}\n\n"
            f"Important: name your theorem exactly `llm_outcome_{left_bot}_vs_{right_bot}` "
            f"to avoid clashing with existing library theorems."
        )

    # Always inject the bot definitions so the agent doesn't need to fetch them manually.
    # Try the standard path first, then the LlmGenerations subfolder.
    bot_defs: list[str] = []
    import_lines: list[str] = []
    for bot in dict.fromkeys([left_bot, right_bot]):  # deduplicate, preserve order
        for candidate, module in (
            (f"Bots/{bot}.lean", f"PrisonersDilemma.Bots.{bot}"),
            (f"Bots/LlmGenerations/{bot}.lean", f"PrisonersDilemma.Bots.LlmGenerations.{bot}"),
        ):
            try:
                src = _read_lean(candidate)
                bot_defs.append(f"--- {candidate} ---\n```lean\n{src}\n```")
                import_lines.append(f"import {module}")
                break
            except OSError:
                pass
    if bot_defs:
        parts.append(
            "Bot definitions (for reference only — DO NOT redefine these in your proof file):\n\n"
            + "\n\n".join(bot_defs)
        )
    if import_lines:
        parts.append(
            "Use exactly these import lines in your proof file to reference the bots:\n\n"
            "```lean\n" + "\n".join(import_lines) + "\n```"
        )

    parts.append(
        f"Known outcome theorems involving these bots:\n{known_theorems_summary}"
    )

    if few_shot_files:
        parts.append("Here are relevant existing theorem files for reference:\n")
        for filename, source in few_shot_files:
            parts.append(f"--- {filename} ---\n```lean\n{source}\n```")

    parts.append(
        "Use the `run_lean_proof` tool to check your proof. "
        "Iterate until it compiles cleanly, then output the final source and say PROOF COMPLETE."
    )

    return "\n\n".join(parts)


# ---------------------------------------------------------------------------
# Bot writer prompts
# ---------------------------------------------------------------------------

_BOT_EXAMPLES = [
    "Bots/CooperateBot.lean",
    "Bots/DefectBot.lean",
    "Bots/TitForTatBot.lean",
    "Bots/MirrorBot.lean",
    "Bots/DBot.lean",
    "Bots/OBot.lean",
    "Bots/EBot.lean",
    "Bots/CupodBot.lean",
]


def build_bot_system_prompt() -> str:
    program_src = _read_lean("Program.lean")
    dynamics_src = _read_lean("Dynamics.lean")

    examples: list[str] = []
    for path in _BOT_EXAMPLES:
        try:
            src = _read_lean(path)
            examples.append(f"-- {path}\n```lean\n{src}\n```")
        except OSError:
            pass

    examples_block = "\n\n".join(examples)

    return f"""\
You are an expert Lean 4 bot designer for the open-source game theory project.

# The Prog language

Bots are programs written in the `Prog` language defined in Program.lean. \
Each bot is a Lean definition `def BotName : Prog := ...`.

-- Program.lean
```lean
{program_src}
```

-- Dynamics.lean (how Prog terms are evaluated)
```lean
{dynamics_src}
```

# Prog constructor reference

| Constructor | Meaning |
|---|---|
| `.const a` | Always play action `a` (C or D), ignoring the opponent |
| `.sim p q` | Simulate program `p` against opponent `q`; returns the action `p` would play |
| `.ite guard action p q` | Run `guard`; if it returns `action`, evaluate `p`, else evaluate `q` |
| `.bot p` | Closed reference to bot `p` — substitution does not descend inside |
| `.self` | Placeholder for "my own source code" — resolved by `subst` |
| `.opp` | Placeholder for "the opponent's source code" — resolved by `subst` |
| `.search k φ p q` | If the proof oracle can verify formula `φ` within a budget of `k` characters, run `p`, else `q` |

`φ` above is a `Formula` (see Program.lean). The relevant `Formula` constructors are
`.plays p q a` ("`p(q.source) == a`"), `.impl`, `.neg`, `.box n φ` ("`φ` is provable
within budget `n`"), and `.eq p q` — a **structural-identity** guard meaning "probe `p`
(typically `.opp`) is literally the same program as the frozen literal target `q`".
`subst` resolves the probe `p` but does not descend into the literal `q`. Use `.eq` for
strategies that test whether the opponent is a specific named bot.

# Existing bots (few-shot examples)

{examples_block}

# Your task

Given a natural language description of a strategy, write a valid Lean 4 bot definition file.
Use the `run_lean_build` tool to check your bot compiles. Fix errors and iterate.
Use the `read_library_file` tool to inspect any existing bot for reference.

# Rules
- The file must compile with zero errors (exit code 0 from `run_lean_build`).
- The bot must be in namespace `PD.Bots`.
- Import only `PrisonersDilemma.Program` and bot files you reference via `.bot`.
- Do not use `sorry` or any placeholder.
- **Search budget must be a parameter, not a literal.** If your bot uses `.search`, the
  bot definition MUST take a `Nat` parameter (conventionally `k`) and pass it as the
  search budget, e.g. `def MyBot (k : Nat) : Prog := .search k ...`. Hardcoded budgets
  like `.search 1000 ...` are NOT allowed — downstream theorems quantify over `k`, and a
  fixed literal breaks that. Bots without `.search` (e.g. `CooperateBot`) take no parameter.
- When the bot compiles cleanly, output the final Lean source inside a ```lean ... ``` code fence and say "BOT COMPLETE".
"""


def bot_request_message(bot_name: str, strategy_description: str) -> str:
    return f"""\
Write a Lean 4 bot definition for the following strategy:

**Bot name:** `{bot_name}`

**Strategy:** {strategy_description}

The bot definition should go in the namespace `PD.Bots` and follow this structure:

```lean
import PrisonersDilemma.Program
-- (add more imports if your bot references other bots via .bot)

open PD
namespace PD.Bots

def {bot_name} : Prog :=
  -- your Prog expression here

end PD.Bots
```

Use the `run_lean_build` tool with `bot_name = "{bot_name}"` to check your definition compiles. \
Iterate until it compiles cleanly, then output the final source and say BOT COMPLETE.
"""
