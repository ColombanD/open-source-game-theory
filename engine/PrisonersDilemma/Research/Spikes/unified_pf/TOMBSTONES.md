# unified_pf spikes — RETIRED (Phase 1 of the `Pf`-only migration, 2026-07-14)

All three spikes in this directory did their job and were deleted; their content is now the
*engine itself*. Recorded here so the reasoning survives the files.

| spike | what it proved | where it lives now |
|---|---|---|
| `UnifiedPfSpike.lean` | The merged proof-term type typechecks on a toy `Formula`, and collapses the CIMCIC double induction to one. | Superseded by the real thing: `PrisonersDilemma/Derivation.lean` (`Pf`). |
| `PfEngineSpike.lean` | The real `Pf` over the real engine + the EXACT round-trip `Pf k φ ↔ Provable k φ`; the CIMCIC exclusion in one flat named induction; DupocBot self-cooperation (critch22 Thm 3.7) end-to-end in `Pf`. | The type + eliminators are `Derivation.lean`; the round-trip is superseded by `LegacyS.lean`'s `legacy_iff_live` (same theorem, against the frozen `S`); the demo ports become the library's normal style in Phase 3. |
| `PfMutualInductSpike.lean` | Making `Pf` primitive re-mutualizes it, so `induction … with` breaks (`fail_if_success`) — and a hand-derived `@[elab_as_elim]` eliminator restores named arms. **This is why the migration shipped `Pf.induct`/`PlaysProof.induct` in the same commit as the merged type.** | `Derivation.lean` §4 (`Pf.induct`, `PlaysProof.induct`). The regression it predicted is now real; the cure it prototyped is now load-bearing. |

The one live artifact in this directory is **`LegacyS.lean`** — the frozen pre-migration `S` plus
`legacy_iff_live : Legacy.Provable k φ ↔ PD.Pf k φ`, the theorem that makes the migration
meaning-preserving. It retires in Phase 4.5, once the metatheory is `Pf`-only.

See `Research/Notes/PF_ONLY_ROADMAP.md`.
