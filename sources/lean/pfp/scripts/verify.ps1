param([string]$LakePath = '')
$ErrorActionPreference = 'Stop'
$project = Split-Path $PSScriptRoot -Parent
$formalRoot = Split-Path $project -Parent
. (Join-Path $PSScriptRoot 'local-modules.ps1')
$workspace = Split-Path $formalRoot -Parent
if (!$LakePath) { $LakePath = Join-Path $workspace 'tmp/lean-runtime/lean-4.24.0-windows/bin/lake.exe' }
$LakePath = (Resolve-Path -LiteralPath $LakePath).Path
$logs = Join-Path $project 'verification'
New-Item -ItemType Directory -Force -Path $logs | Out-Null
$results = [System.Collections.Generic.List[object]]::new()
function RunCheck([string]$directory, [string[]]$arguments, [string]$log, [string]$auditFile = '') {
    Push-Location $directory
    try {
        & $LakePath @arguments *> (Join-Path $logs $log)
        $code = $LASTEXITCODE
        $results.Add([ordered]@{directory=$directory; executable=$LakePath; arguments=$arguments; exit_code=$code; log=$log})
        $results | ConvertTo-Json -Depth 8 | Set-Content -Encoding utf8 -LiteralPath (Join-Path $logs 'results.json')
        if ($code -ne 0) { Get-Content -LiteralPath (Join-Path $logs $log); throw "Failed: $log" }
        if ($auditFile) {
            $expected = [regex]::Matches((Get-Content -Raw -LiteralPath $auditFile),'(?m)^#print axioms ').Count
            $output = Get-Content -Raw -Encoding utf8 -LiteralPath (Join-Path $logs $log)
            $reports = [regex]::Matches($output,"'[^']+' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
            if ($reports.Count -ne $expected) { throw "Expected $expected axiom reports, found $($reports.Count)" }
            foreach ($report in $reports) {
                foreach ($axiom in ($report.Groups[1].Value -split ',')) {
                    if ($axiom.Trim() -and $axiom.Trim() -notin @('propext','Classical.choice','Quot.sound')) { throw "Unapproved axiom: $axiom" }
                }
            }
        }
        Write-Output "PASS $log"
    } finally { Pop-Location }
}
RunCheck $project @('env','lean','--version') 'lean-version.txt'
# Build exactly the common audit's import closure without executing its
# expensive #print commands twice. Each command from the original catalogue
# runs exactly once in checked shards with exact name, count and axiom checks.
$commonAudit = Join-Path $formalRoot 'common/ThesisCommon/PFPAudit.lean'
$commonImports = Join-Path $formalRoot 'common/ThesisCommon/PFPAuditImports.lean'
$importLines = @(Get-Content -Encoding utf8 -LiteralPath $commonAudit | Where-Object { $_ -match '^import ' })
if (!$importLines.Count) { throw 'PFPAudit has no imports to build.' }
$importSource = "/- Generated from PFPAudit.lean by pfp/scripts/verify.ps1. Import-only build target. -/`n" + ($importLines -join "`n") + "`n"
if (!(Test-Path -LiteralPath $commonImports) -or (Get-Content -Raw -Encoding utf8 -LiteralPath $commonImports) -ne $importSource) {
    [System.IO.File]::WriteAllText($commonImports, $importSource, [System.Text.UTF8Encoding]::new($false))
}
# Capture the exact closure and build configuration after the intentional
# PFPAuditImports write and before any build or axiom audit.
$beforeSnapshot = @(Get-VerificationInputSnapshot $formalRoot)
$beforeSnapshotPath = Join-Path $logs 'input-snapshot-before.json'
$beforeSnapshot | ConvertTo-Json -Depth 8 | Set-Content -Encoding utf8 -LiteralPath $beforeSnapshotPath
RunCheck (Join-Path $formalRoot 'common') @('build','ThesisCommon.PFPAuditImports') 'common-build.txt'
$commonShardResult = & (Join-Path $PSScriptRoot 'check-axiom-shards.ps1') `
    -LakePath $LakePath -Directory (Join-Path $formalRoot 'common') `
    -AuditFile $commonAudit -LogFile (Join-Path $logs 'common-axiom-audit.txt')
$results.Add([ordered]@{
    directory=(Join-Path $formalRoot 'common'); executable=$LakePath;
    execution='each axiom command checked exactly once in bounded parallel shards';
    catalogue=$commonAudit; manifest=$commonShardResult.manifest;
    reports=$commonShardResult.reports; shard_count=$commonShardResult.shard_count;
    exit_code=$commonShardResult.exit_code; log='common-axiom-audit.txt'
})
$results | ConvertTo-Json -Depth 8 | Set-Content -Encoding utf8 -LiteralPath (Join-Path $logs 'results.json')
Write-Output 'PASS common-axiom-audit.txt'
# Lake 4.24's default library glob is the root module and its imports. PFP.lean
# does not import PFP.Audit, so this full configured project build is retained.
RunCheck $project @('build') 'build.txt'
$paperAudit = Join-Path $project 'PFP/Audit.lean'
$paperShardResult = & (Join-Path $PSScriptRoot 'check-paper-audit.ps1') `
    -LakePath $LakePath -Directory $project -AuditFile $paperAudit `
    -LogFile (Join-Path $logs 'axiom-and-statement-audit.txt')
$results.Add([ordered]@{
    directory=$project;executable=$LakePath;
    execution='all statement commands retained; each axiom command checked exactly once in bounded parallel shards';
    catalogue=$paperAudit;manifest=$paperShardResult.manifest;
    reports=$paperShardResult.reports;statement_commands=$paperShardResult.statement_commands;
    shard_count=$paperShardResult.shard_count;exit_code=$paperShardResult.exit_code;
    log='axiom-and-statement-audit.txt'
})
$results | ConvertTo-Json -Depth 8 | Set-Content -Encoding utf8 -LiteralPath (Join-Path $logs 'results.json')
Write-Output 'PASS axiom-and-statement-audit.txt'
# Re-resolve all local imports after checking. Shared projects may have changed.
$afterSnapshot = @(Get-VerificationInputSnapshot $formalRoot)
$afterSnapshot | ConvertTo-Json -Depth 8 | Set-Content -Encoding utf8 -LiteralPath (Join-Path $logs 'input-snapshot-after.json')
Assert-VerificationSnapshotsEqual $beforeSnapshot $afterSnapshot
$manifest = Get-Content -Raw -LiteralPath (Join-Path $project 'source-manifest.json') | ConvertFrom-Json
foreach ($record in $manifest.files) {
    if ((Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $project $record.file)).Hash -ne $record.sha256) { throw "Source changed: $($record.file)" }
}
& (Join-Path $PSScriptRoot 'update-records.ps1') -VerifiedSourceSnapshot $beforeSnapshotPath
[ordered]@{
    date='2026-10-03'; lean='4.24.0'; mathlib='f897ebcf72cd16f89ab4577d0c826cd14afaafc7';
    result='PASS'; completed_original_results=@('2.3','2.5','3.1','3.2','3.3','3.4','3.6','3.7','3.8','3.9','3.10','3.11','3.12','3.13','3.14','3.15','3.16','3.17','3.18','3.19','3.20','3.21','3.22','3.23','3.24','3.25','3.26','3.27','4.1','4.3','4.5','4.6','4.7','4.9','4.10','4.12','4.13','4.14','4.15','4.16','4.17','4.18','4.19','4.20','4.21','4.22','4.23','4.24','4.25','4.26','4.28','4.29','4.31','5.1','5.3','5.4','5.6','5.7','5.8','5.9','5.10','5.11','5.12','5.13','5.14','5.15','6.5','6.8','6.9','6.10','6.11','7.1','A.1','B.1','B.2','B.3','B.4');
    corrected_result='2.6 with Nontrivial E'; counterexample='printed 2.6 for Fin 0 -> real';
    context_restored_results=@('4.27 with section uncountability','4.30 with section uncountability');
    excluded_by_user=@('4.32 unspecified iterated versions'); remarks_optional_by_user=$true;
    partial_results=@('2.1 printed non-strict infimum-attainment equivalence remains unproved; actual-map definition, forward/strict witnesses and correct all-epsilon equivalence proved');
    requested_theorem_targets_complete=$true;
    source_corrections=@('2.6 nontrivial-space repair and exact printed zero-space counterexample','4.27/4.30 uncountable section context restored; both unrestricted printed targets have checked countable-index counterexamples','5.2 user-corrected separable version proved; remarks optional');
    whole_manuscript_complete=$false; statement_phase_complete=$false;
    allowed_axioms=@('propext','Classical.choice','Quot.sound')
} | ConvertTo-Json -Depth 8 | Set-Content -Encoding utf8 -LiteralPath (Join-Path $logs 'summary.json')
Write-Output 'Verified partial formalisation; manuscript-wide completion is not claimed.'
















