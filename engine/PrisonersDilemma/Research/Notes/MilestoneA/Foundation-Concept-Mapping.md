# Foundation Concept Mapping (Milestone A)

Date: 2026-04-14
Milestone: A - Foundation Integration Layer
Status: Draft

## Purpose
Map project concepts to FormalizedFormalLogic/Foundation modules and theorem assets.

## Mapping Table

| Project Concept | Foundation Candidate | Type (Module/Theorem/Def) | Match Level (Exact/Near/Unknown) | Local Glue Needed | Notes |
|---|---|---|---|---|---|
| Modal syntax and formula layer | Foundation.Modal.Axioms; Foundation.Modal.Entailment.Basic; Foundation.Modal.Hilbert.Normal.Basic | Module | Exact | No | Core modal formula/axiom and entailment infrastructure is directly present in Foundation root exports. |
| Semantics (frames/models/truth relation) | Foundation.Modal.Kripke; Foundation.Modal.Kripke.Hilbert; Foundation.Logic.Semantics | Module | Exact | No | Kripke frame/model classes and semantic satisfaction pipeline are available for modal logics. |
| Provability logic core | Foundation.ProvabilityLogic.Arithmetic; Foundation.ProvabilityLogic.GL.Soundness; Foundation.ProvabilityLogic.Realization | Module | Exact | Near (thin wrappers) | Theory-relative provability logic and realizations exist; engine will likely need naming wrappers only. |
| GL hooks | Foundation.Modal.Entailment.GL; Foundation.Modal.Kripke.Logic.GL.Completeness; theorem LO.ProvabilityLogic.GL.arithmetical_completeness_iff | Module + Theorem | Exact | No | Includes Hilbert-level GL entailment plus Kripke and arithmetic completeness/soundness bridge. |
| Grz hooks | Foundation.Modal.Entailment.Grz; Foundation.Modal.Kripke.Logic.Grz.Completeness; theorem LO.ProvabilityLogic.Grz.arithmetical_completeness_iff | Module + Theorem | Exact | Near (bridge lemma names) | Grz has both modal and provability-level completeness endpoints. |
| Boxdot translation support | Foundation.Modal.Boxdot.Basic; Foundation.Modal.Boxdot.GL_Grz; theorem LO.Modal.iff_provable_boxdot_GL_provable_Grz | Module + Theorem | Exact | No | Direct GL ↔ Grz boxdot correspondence already formalized. |
| Arithmetical completeness entry points | theorem LO.ProvabilityLogic.GL.arithmetical_completeness_iff; theorem LO.ProvabilityLogic.Grz.arithmetical_completeness_iff; theorem LO.ProvabilityLogic.provabilityLogic_eq_GL_of_sigma1_sound | Theorem | Exact | Near (instantiation wrappers) | These are the main handoff points from modal provability to arithmetic realizations. |
| Lemma 3.6 role candidate (Critch-shape) | Primary: LO.ProvabilityLogic.GLPlusBoxBot.arithmetical_completeness_iff; Secondary: LO.Modal.Logic.iff_provable_GL_provable_box_S; Bridge: LO.Modal.iff_provable_boxdot_GL_provable_Grz | Theorem family | Near | Yes | Candidate role: bounded/parameterized provability transfer for large k style arguments; final pick depends on exact Critch Lemma 3.6 statement encoding. |

## Notes
- Foundation identifiers above are taken from the upstream Foundation repository (FormalizedFormalLogic/Foundation, main branch).
- The "Lemma 3.6 role" row is intentionally marked Near until the Critch statement is encoded as a Lean theorem signature in this project.
- Prefer semantic-role mapping first, exact naming second.
- If multiple candidates exist, list all and mark preferred one.

## Review Checklist
- [x] All minimum categories covered
- [x] Match level set for each row
- [x] Glue necessity marked for each row
- [x] Ambiguities recorded as explicit questions
