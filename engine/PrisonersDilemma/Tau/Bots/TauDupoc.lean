import PrisonersDilemma.Tau.Roster

/-!
# TauDupoc — the Löbian cooperator, lifted

One `prove` stage with the SELF target: "search for a proof that the opponent,
seeing ME, cooperates." Base DupocBot's guard, with the severed `.opp` wire replaced
by the signal's hypotheses. The zoo's only self-prober, which buys it the two
interesting cells:

* **the quine** — at point mass on itself, the compiler cannot embed the instance in
  its own guard, so it emits the pronoun `.plays .self .self .C` and bounded Löb
  closes the fixpoint past a budget threshold (`ps_probe_quine`; its phase theorem
  is Löb-GATED, `∃ k₂, ∀ k > k₂, …`);
* **the floor** — its EBot entry reads 0 although `inst ebot dupoc` REALLY
  cooperates: that cooperation hides behind a failed exploit-search, so no ≤k
  certificate exists (the Gödelian pair in `Tau/Certs.lean`/`Tau/InstCerts.lean`).
  Hence its boundary `θ ≤ wC + wTs + wTp + wL` honestly EXCLUDES `w .ebot` — the tau
  image of base `outcome_DupocBot_vs_EBot = (D, C)`.
-/

namespace PD.Tau

/-- τ(DupocBot): "prove the opponent (seeing me) cooperates; then C; else D." -/
def tauDupocSpec : Spec Tmpl := ⟨[⟨.prove, .self, .C, .C⟩], .D⟩

end PD.Tau
