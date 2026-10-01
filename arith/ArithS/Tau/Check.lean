import ArithS.Tau.Rows.Coop
import ArithS.Tau.Rows.Defect
import ArithS.Tau.Rows.TftSim
import ArithS.Tau.Rows.DBot
import ArithS.Tau.Rows.OBot
import ArithS.Tau.Rows.CupodTroll
import ArithS.Tau.Rows.EBot
import ArithS.Tau.Rows.Dupoc
import ArithS.Tau.Rows.Cupod
import ArithS.Tau.Rows.CIMCIC
import ArithS.Tau.Rows.DIMCID
import ArithS.Tau.Rows.Prudent
import ArithS.Tau.Rows.MaxConfidence
import ArithS.Tau.Rows.MinConfidence
import ArithS.Tau.Lint

/-!
# ArithS.Tau.Check — the build-time census of the PA-`S'` tau rows (`lake build ArithSTauCheck`)

Its own lake library root (in `defaultTargets`), like `Outcome/Check.lean`: a command cannot sit in the root
index. Imports every `Tau/Rows/<Tmpl>.lean` and runs `#check_tau_rowsA` (`Tau/Lint.lean`): every tagged row and
floor bit is on its template with a name that agrees with its statement, no bit is stated twice, the floor bits
are exactly `‡` cells of the table. STRICT since Phase 3f (2026-10-02): 14 rows, 149 row slots, 47 floor bits,
196/196 — every coverage gap is a build error (the last bit, `dimcid × ebot`, landed when the budget abstraction
descended into systems: `Tau/ClosedWatch3.dimcid_ebot_D`). The exporter
(`Outcome/Export.lean`) imports THIS module, so what it writes to `app/generated/sprime_tau_rows.json` has passed
the gate.
-/

#check_tau_rowsA strict
