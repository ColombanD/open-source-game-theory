---
name: onedrive-lake-replay-timeout
description: "lake build fails with \"Replaying <Mod>… time expired (error code 60)\" on OneDrive — fix by building the stuck target directly"
metadata: 
  node_type: memory
  type: project
  originSessionId: e0fe1799-fa75-4928-b015-101b623163c3
  modified: 2026-07-28T08:45:13.547Z
---

On this machine the repo lives in a OneDrive-synced folder, and full `lake build`
(3237 jobs) intermittently fails with `✖ Replaying Mathlib.Init` (or Plausible / Qq /
LeanSearchClient) + `error: time expired (error code: 60, operation timed out)`.

**Why:** these are Lake's log-replay bookkeeping steps on already-built DEPENDENCY
artifacts; under heavy parallel I/O OneDrive stalls the file reads/locks past Lake's
timeout. The project's own modules compile fine — the failure is NOT a code error.

**How to apply:** don't debug the Lean code. Re-run `lake build` (each pass clears
some), and for a target stuck at the same job number repeatedly, build it directly
once — `lake build +Mathlib.Init` — then re-run the full `lake build` (observed
2026-07-28: direct build succeeded in 49 jobs, full build then green).

Mathlib is required because `Base/Asymptotics.lean` imports `Mathlib.Tactic`
(log₂ arithmetic) — the whole Mathlib job graph rides on that one import.

**Waiting on a build (2026-08-27):** `pgrep -x lake` also matches the VSCode extension's `lake serve`, so an `until ! pgrep -x lake` loop NEVER exits (cost an idle hour). Match the command line: `pgrep -f 'lake build'`, or just run the build in a background Bash and read its notification.

**2026-09-09 addendum (arith/ package, Foundation from source):** a fresh `lake build` of
Foundation under OneDrive STALLED outright — two `lean` compiles (Term/Basic.lean,
Superexp.lean) sat in uninterruptible disk wait (`state U`/"stuck") for 54 min with ~7 min
CPU, log untouched. Fix that keeps the sources in place for the IDE: relocate ONLY the
build dir — `rm -rf arith/.lake; ln -s ~/wt/arith-lake arith/.lake` — so all olean I/O is
on local disk; re-run `lake update` (mathlib cache re-downloads, ~10 min). Check for the
stall with `ps -o pid,etime,%cpu,state -p <lean pids>`: low %cpu + state U = OneDrive.
**And never compile Foundation locally**: `lake build --try-cache ArithS` downloads the
prebuilt Foundation artifacts in ~90 s (discovered 2026-09-09 after an hour of stalled
compiles). One ArithS file check needs ~5 GB resident; with swap full it thrashes.
