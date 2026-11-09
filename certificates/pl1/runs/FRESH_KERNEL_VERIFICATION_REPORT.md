# Fresh A/B/C/D kernel verification

The complete fresh verification **passed**. All 3,473 imported non-toolchain
modules were rebuilt from source in an initially empty artifact directory,
followed by successful official `leanchecker --fresh --verbose PL1FreshAudit`
and raw theorem/type/axiom inspection. All original sources, copied sources,
compiled artifacts and replay inputs remained unchanged.

The source rebuild, fresh kernel replay and raw inspection completed on
3 October 2026. The process disconnected during the last identity check.
Completion resumed on 19 October 2026: all recorded sources, artifacts,
toolchain inputs and native-check evidence were revalidated by fresh reads
and hashes before sealing. The successful native kernel replay and inspection
were retained from 3 October; they were not rerun on 19 October. The original
interrupted records are preserved beside the recovered final checkpoint.

The rebuild covers 292 delivered A/B/C/D/BanLat modules, 2,924 Mathlib modules
and 257 other package modules. Native source compilation took
321.02 minutes; kernel replay took
14.63 minutes. Every import outside the
pinned toolchain resolved to an artifact produced by this run. No old compiled
project, BanLat, Mathlib or other package artifact was used.

The inspector checked all ten real/complex endpoints against their exact
reviewed statement constants, five general theorem declarations, and stored
types and bodies of 43 definitions. It traversed the raw type/value dependency
graph for 208 requested claim records and every eligible declaration originating
in the 292 delivered modules. Reachable axioms were limited to `propext`,
`Classical.choice` and `Quot.sound`, with no unsafe, partial or missing logical
dependency and no project-origin axiom declaration.

The checker imported 3474 fresh modules, including the
import-only audit root, and 1552 bundled
toolchain modules. Its fresh replay begins with an empty kernel environment and
rechecks the merged imported declarations, including those bundled libraries.
Lean's compiler, bundled-library binaries, runtime and operating system remain
trusted; this is not a compiler bootstrap or verification by an independently
implemented kernel. Optional style linters and Lake cache hooks were not run.
The checker excludes unsafe and partial declarations, which the separate
inspection inventories; delivered exclusions must be verified compiler
recursion companions.

The preserved reports disclose the Windows path-length failure during widget
cache preparation and its recovery. Final-check attempt 1 stopped because the
report parser incorrectly expected ten fields in the four-field MODULE_PART
record. Native import inventory and the audit-root compilation had passed;
kernel replay had not started. The original driver and failure evidence were
preserved, the field-count parser was corrected, and the final checks were
rerun as attempt 2. Fresh npm installation and widget source
compilation passed, without reusing generated widget bundles. All unsuccessful
attempts, if any, remain recorded alongside the successful native exits.

The complex supplementary target proves the reviewed underlying-real lattice
obstruction. The separate bridge to complex Banach-lattice terminology is not
formalised. Kernel checks verify these exact formal statements; comparison
with the human paper remains a separate mathematical review.

## Saved certificates and evidence

- `CERTIFICATE_SUMMARY.json`: final machine-readable scope and results.
- `verification/Fresh-20261003T133417Z/source-build-status.json`: every native
  compilation result, resolved imports, source and artifact hashes.
- `verification/Fresh-20261003T133417Z/modules/`: full per-module commands,
  dependency resolution output, compiler stdout/stderr and exit codes.
- `verification/Fresh-20261003T133417Z/kernel-replay-2/`: official checker
  command, complete logs, native exit and retained trust boundaries.
- `verification/Fresh-20261003T133417Z/inspection-2/`: exact theorem types,
  definition bodies, raw transitive axiom inspection and exclusion inventory.
- `verification/Fresh-20261003T133417Z/final-checks-2-recovery-20261019/`: recovered final source/artifact/input
  identity checkpoints and the complete imported-artifact inventory.
- `FULL_CERTIFICATES.zip`: sources, all newly produced Lean proof artifacts,
  actual retained kernel inputs, audit scripts and complete saved evidence.
- `FULL_CERTIFICATES.zip.sha256`: archive digest.
- `CERTIFICATE_FILES_SHA256.json`: every archive member's hash and size.

All evidence is local. No public website, deployment or remote repository was
changed. The public release remains at `008c8a6c725677dffb47d19183d002c27dd41e38`.
