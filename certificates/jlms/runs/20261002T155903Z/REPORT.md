# JLMS fresh verification — 20261002T155903Z

The isolated JLMS compilation and fresh Lean-kernel replay both passed.

- 235 JLMS Lean source files, unchanged in the author's project.
- 1219 explicit axiom reports; 3065 project declarations examined in the full axiom traversal.
- Only propext, Classical.choice and Quot.sound occurred. No sorryAx or additional mathematical axioms.
- 4940 imported modules; 396740 safe, total constants in the replayed environment.
- Lean (version 4.24.0, x86_64-w64-windows-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)
- Mathlib: f897ebcf72cd16f89ab4577d0c826cd14afaafc7.
- lean4checker: da26eb05e9959402afcb9bd6dfe5dc4f700f70d6 (v4.24.0, unmodified official source).

All six main results (1.1, 1.3, 1.4, 1.5, 1.6, 1.7) have complete proof declarations. Every numbered passage has a correspondence note. Supporting results retain their displayed hypotheses; a checked supporting theorem is not a certificate for a stronger prose statement.

A separate fresh kernel replay also passed for all 3065 JLMS declarations and their complete logical dependencies: 41158 declarations in total. It uses the unmodified replay implementation from the same pinned lean4checker version; check_project_kernel.py records the small driver and its exact commands.


The full Pełczyński theorem (1.10), the full cited statements in 3.1, 3.2 and 9.3, and some discussions and examples are outside the recorded theorem scope. The consequence of the ordinal classification needed for 1.3 is proved.

## Reproduction

Run `fresh_check.py`, then `attach_records.py` from the reader's verification directory with Python. The scripts rebuild a new JLMS copy, run Audit.lean, build the pinned checker and execute `lean4checker --fresh --verbose PaperLeanKernel`. The wrapper imports JLMS; the fresh mode starts with an empty environment and includes imported library declarations. The checker excludes unsafe and partial program declarations and uses Lean's own kernel, not an independent implementation.

JLMS compilation starts without any JLMS build products. Pinned dependency build products are reused and then included in the fresh kernel replay. The closure manifest hashes the compiled files present after verification; the exact commands, durations, source hashes and dependency revisions are recorded in run.json. The original Lean sources are never edited.

The Lake warning about a changed packages directory comes from pointing the copied project at the existing pinned libraries. Their revisions and tracked sources are checked before and after the run. No dependency update is performed.

The manuscript is the author's provided ZIP, with the previously authorised correction to the definition of vanishing at infinity. Kernel acceptance checks the formal declarations; the correspondence notes document their relation to the mathematical prose.
