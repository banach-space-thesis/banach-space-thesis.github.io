# Derived portable fresh-kernel verification snapshot

The imported proof objects, native Lean runtime/DLLs, mathematical sources and
dependency manifests have exactly the bytes recorded in the parent certificate's
pinned SHA256 inventory. The derivation copied all parent files with native
File.Copy and checked every destination against that inventory. Only checker,
reproduction tooling, metadata, instructions and derivation evidence changed.
The old checker, metadata and inventory remain under evidence/derivation/.

With PowerShell 7 on Windows:

```powershell
& .\Verify-Integrity.ps1 -ExpectedManifestHash '<independently recorded digest>'
& .\Replay.ps1 -ExpectedManifestHash '<independently recorded digest>'
```

Replay uses only modules/ for imported objects and the saved native executable.
It checks every imported declaration, including unsafe/partial bodies, into a
fresh empty kernel environment and tests a corrupted proof. Then it verifies
actual resolver paths/facets/counts, freshly runs the foundational axiom audit
and numbered statements, checks paper/Lean provenance, and repeats full integrity.
Existing output directories are never reused. Every attempt retains its logs,
result records, reproduction scripts and hashes in a new external replay folder.

Axioms have their types checked and remain assumptions. Source snapshots are
provenance; the kernel replay consumes saved proof objects. SHA256 inventories
are integrity records, not digital signatures or self-authenticating attestations.
The independently pinned digest is the external trust anchor.

To derive this bundle again, use tools/Derive-KernelCertificate.ps1 with the
original certificate, its pinned digest, the corrected checker and its pinned
digest. Pass this bundle's Verify-KernelCertificateFast.ps1 and Fast-Replay.ps1
via -NativeIntegritySource and -FastReplaySource. A new dated directory is required.
