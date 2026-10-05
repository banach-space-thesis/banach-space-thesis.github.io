param(
    [Parameter(Mandatory)][string]$LakePath,
    [Parameter(Mandatory)][string]$Directory,
    [Parameter(Mandatory)][string]$AuditFile,
    [Parameter(Mandatory)][string]$LogFile
)
$ErrorActionPreference = 'Stop'
if (!(Get-Command RemoveLeanComments -ErrorAction SilentlyContinue)) {
    . (Join-Path $PSScriptRoot 'local-modules.ps1')
}
$originalHash = (Get-FileHash -LiteralPath $AuditFile -Algorithm SHA256).Hash
$lines = @((RemoveLeanComments (Get-Content -Raw -Encoding utf8 -LiteralPath $AuditFile)) -split '\r?\n' |
    Where-Object { $_.Trim() })
$imports = @($lines | Where-Object { $_ -match '^import [A-Za-z0-9_.]+$' })
$axioms = @($lines | Where-Object { $_ -match '^#print axioms [A-Za-z0-9_.]+$' })
$statements = @($lines | Where-Object { $_ -match '^#(?:check|print) [A-Za-z0-9_.]+$' })
if (!$imports.Count -or !$axioms.Count -or !$statements.Count -or
    $imports.Count + $axioms.Count + $statements.Count -ne $lines.Count) {
    throw 'Paper partitioning requires only imports, declaration checks/prints and axiom prints; no other commands may be dropped.'
}
$logDirectory = Split-Path $LogFile -Parent
New-Item -ItemType Directory -Force -Path $logDirectory | Out-Null
$statementSource = Join-Path $logDirectory 'paper-statement-audit.lean'
$statementLog = Join-Path $logDirectory 'paper-statement-audit.txt'
$axiomSource = Join-Path $logDirectory 'paper-axiom-audit.lean'
$axiomLog = Join-Path $logDirectory 'paper-axiom-audit.txt'
[IO.File]::WriteAllText($statementSource, (($imports + $statements) -join "`n") + "`n", [Text.UTF8Encoding]::new($false))
[IO.File]::WriteAllText($axiomSource, (($imports + $axioms) -join "`n") + "`n", [Text.UTF8Encoding]::new($false))
$statementHash = (Get-FileHash -LiteralPath $statementSource -Algorithm SHA256).Hash
$axiomHash = (Get-FileHash -LiteralPath $axiomSource -Algorithm SHA256).Hash
Push-Location $Directory
try {
    & $LakePath env lean $statementSource *> $statementLog
    $statementExit = $LASTEXITCODE
    if ($statementExit -ne 0) {
        Get-Content -LiteralPath $statementLog -Tail 25 | Write-Host
        throw "Paper statement checks failed with exit code $statementExit."
    }
} finally { Pop-Location }
Write-Host "PASS paper statement audit ($($statements.Count) commands)"
$shardArguments = @{
    LakePath=$LakePath;Directory=$Directory;AuditFile=$axiomSource;LogFile=$axiomLog
    ShardDirectoryName='paper-axiom-shards';Label='paper'
}
$shardResult = & (Join-Path $PSScriptRoot 'check-axiom-shards.ps1') @shardArguments
foreach ($guard in @(
    @{path=$AuditFile;hash=$originalHash},
    @{path=$statementSource;hash=$statementHash},
    @{path=$axiomSource;hash=$axiomHash}
)) {
    if ((Get-FileHash -LiteralPath $guard.path -Algorithm SHA256).Hash -ne $guard.hash) {
        throw "Paper audit input changed during checking: $($guard.path)"
    }
}
$combined = (Get-Content -Raw -Encoding utf8 -LiteralPath $statementLog) +
    (Get-Content -Raw -Encoding utf8 -LiteralPath $axiomLog)
[IO.File]::WriteAllText($LogFile, $combined, [Text.UTF8Encoding]::new($false))
$manifest = [ordered]@{
    catalogue=$AuditFile;catalogue_sha256=$originalHash
    statement_source=$statementSource;statement_sha256=$statementHash
    statement_log=$statementLog;statement_exit_code=$statementExit
    statement_commands=$statements.Count
    axiom_source=$axiomSource;axiom_sha256=$axiomHash
    axiom_log=$axiomLog;axiom_commands=$axioms.Count
    axiom_manifest=$shardResult.manifest
    note='Every original non-import command checked exactly once; unsupported syntax is rejected before partitioning.'
}
$manifestPath = Join-Path $logDirectory 'paper-audit-manifest.json'
$manifest | ConvertTo-Json -Depth 8 | Set-Content -Encoding utf8 -LiteralPath $manifestPath
[pscustomobject]@{exit_code=0;reports=$axioms.Count;statement_commands=$statements.Count;
    manifest=$manifestPath;shard_count=$shardResult.shard_count}
