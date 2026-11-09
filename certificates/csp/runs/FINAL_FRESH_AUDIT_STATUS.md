# Final fresh Lean audit status — 6 September 2026

All requested mathematical checks passed. Final packaging status: **PASS**.

| Stage | Result |
|---|---|
| 1. Source/environment/target identity | PASS |
| 2. Existing-artifact fresh replay | PASS — exit 0, 598.000 s |
| 3. Imported-dependency and project source reproduction | PASS — exit 0, 6,896.594 s |
| 4. Rebuilt-artifact fresh replay | PASS — exit 0, 833.828 s |
| 5. Endpoint types, definition identity, axioms | PASS — all native exit codes 0 |
| 6. Final source preservation and packaging | PASS — all-member CRC/SHA-256 and final manifests verified |

Both replay invocations used the pinned `lake.exe` and `leanchecker.exe`: `lake env leanchecker --fresh --verbose ComplementedSubspace` in the original project and `lake --no-cache env leanchecker --fresh --verbose ComplementedSubspace` in the reproduction. The source command was `lake --no-cache build +ComplementedSubspace:olean`.

Actual rebuilt coverage: 2,774 primary modules = 177 project/BanLat/root plus 2,597 external modules, including 2,340 Mathlib modules. No precompiled non-toolchain Lean artifacts were reused or fetched. The pinned Lean toolchain and tracked ProofWidgets JavaScript inputs were retained.

Exact endpoints: `ComplementedSubspace.realMainTheorem`, `ComplementedSubspace.realCorollary`, `ComplementedSubspace.realUnconditionalCorollary`, `ComplementedSubspace.realSeparableNonprimarity`, `ComplementedSubspace.complexCorollary`. All five are proved closed declarations at the frozen statement types. Each has exactly `propext`, `Classical.choice`, `Quot.sound`; no additional axiom. The namespace allowlist check covered 2,573 declarations. Source findings include documented external placeholder-generating tactic tools; none introduces an extra axiom dependency into these endpoints.

Lean `4.34.0-rc2` / commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`; Lake `5.0.0-src+6a10ac8`; Mathlib `4cbb42e75a050e830b7cf0f2ae748d7644f59cf7`; BanLat `5c9360ccd9cef27b749f3cabda6348fd2529d1a3`. All nine dependency pins and tracked source bytes are recorded in the report. Each original/reproduced project tree's 233 files and dependency tree's 10,056 tracked files remained unchanged.

Frozen source manifest SHA-256: `875e2219bcfe9ea3c6a66a21fecbb077fc225b47e4ab39a0720f82735fe8fa3a`. Start 10:28:54 UTC; archive-validation.json records the exact final elapsed time and archive digest. No mathematical audit stage remains unfinished after the packaging PASS.

Report: evidence/report.md (also report.html). Raw logs: evidence/*.log and *.command.json. Download bundle: full-fresh-audit-evidence.zip, with internal CONTENTS.sha256 and detached archive-validation.json. Reproduction: evidence/REPRODUCE.md.

Companion location: existing Verification page, `/verification/#extended-fresh-audit`. Website integration/validation is recorded separately after the mathematical audit package is finalized. Everything remains local and unpublished; no uploads or power-setting/shutdown actions occurred. Raw local evidence retains personal Windows paths for review before any eventual public release.

## Completed local website handoff

Completed at 13:15:42 UTC on 6 September 2026, after 2 h 46 min 48.2 s overall. Nothing requested remains unfinished.

The compact “Extended fresh audit” report/download entry is on the existing [Verification page](http://127.0.0.1:4173/verification/#extended-fresh-audit). Only `app/verification/page.tsx` changed among product source files. All 202 other checkpointed, non-generated website files remain byte-identical, including original certificates, source downloads, Results, Definitions and guides. Historical audit descriptions were labelled explicitly as the original run.

Source/guide consistency, lint, TypeScript and production build passed. All 49 local report links returned HTTP 200. The actual served 91,734,840-byte archive download matched SHA-256 `a3ec86982d133dcc694c4fdea8065785c3826fd0c587d37d22443ff47ef5ab24`. Desktop (1440 px) and mobile (390 px) report navigation and layouts passed without page overflow, browser errors or external requests. Evidence: `website-update.json`, `website-qa/website-checks.json`, `website-qa/website-build.command.json` and screenshots.

The completed mathematical audit archive is unchanged; this website handoff record is detached. Local raw logs contain personal Windows paths and usernames; any public release will need a separately labelled privacy review/redacted copy. Nothing was uploaded or published.
