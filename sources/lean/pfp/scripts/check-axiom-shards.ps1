param(
    [Parameter(Mandatory)][string]$LakePath,
    [Parameter(Mandatory)][string]$Directory,
    [Parameter(Mandatory)][string]$AuditFile,
    [Parameter(Mandatory)][string]$LogFile,
    [int]$ChunkSize = 200,
    [int]$Parallelism = 3,
    [string]$ShardDirectoryName = 'common-axiom-shards',
    [string]$Label = 'common'
)
$ErrorActionPreference = 'Stop'
if ($ChunkSize -lt 1 -or $Parallelism -lt 1) { throw 'Invalid audit shard size or concurrency.' }
if ($ShardDirectoryName -notmatch '^[A-Za-z0-9_-]+$') { throw 'Invalid audit shard directory name.' }
if (!(Get-Command RemoveLeanComments -ErrorAction SilentlyContinue)) {
    . (Join-Path $PSScriptRoot 'local-modules.ps1')
}
$auditSource = Get-Content -Raw -Encoding utf8 -LiteralPath $AuditFile
$codeLines = @((RemoveLeanComments $auditSource) -split '\r?\n' | Where-Object { $_.Trim() })
$imports = @($codeLines | Where-Object { $_ -match '^import [A-Za-z0-9_.]+$' })
$prints = @($codeLines | Where-Object { $_ -match '^#print axioms [A-Za-z0-9_.]+$' })
if (!$imports.Count -or !$prints.Count -or $imports.Count + $prints.Count -ne $codeLines.Count) {
    throw 'Sharded auditing requires an import-and-axiom-only catalogue; no other Lean commands may be dropped.'
}
$shardDirectory = Join-Path (Split-Path $LogFile -Parent) $ShardDirectoryName
New-Item -ItemType Directory -Force -Path $shardDirectory | Out-Null
$shards = [System.Collections.Generic.List[object]]::new()
for ($offset = 0; $offset -lt $prints.Count; $offset += $ChunkSize) {
    $index = $shards.Count
    $end = [Math]::Min($offset + $ChunkSize, $prints.Count)
    $commands = @($prints[$offset..($end - 1)])
    $stem = 'shard-' + $index.ToString('D3')
    $sourcePath = Join-Path $shardDirectory ($stem + '.lean')
    [System.IO.File]::WriteAllText($sourcePath,
        (($imports + $commands) -join "`n") + "`n", [System.Text.UTF8Encoding]::new($false))
    $shards.Add([pscustomobject]@{
        index = $index; source = $sourcePath
        sha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $sourcePath).Hash
        stdout = Join-Path $shardDirectory ($stem + '.stdout.txt')
        stderr = Join-Path $shardDirectory ($stem + '.stderr.txt')
        names = @($commands | ForEach-Object { $_.Substring(14).Trim() })
        process = $null; exit_code = $null; reports = 0
    })
}
$active = [System.Collections.Generic.List[object]]::new()
$next = 0
$completed = 0
try {
    while ($completed -lt $shards.Count) {
        while ($next -lt $shards.Count -and $active.Count -lt $Parallelism) {
            $shard = $shards[$next]
            $startArguments = @{
                FilePath = $LakePath; WorkingDirectory = $Directory
                ArgumentList = @('env', 'lean', ('"' + $shard.source + '"'))
                RedirectStandardOutput = $shard.stdout; RedirectStandardError = $shard.stderr
                WindowStyle = 'Hidden'; PassThru = $true
            }
            $shard.process = Start-Process @startArguments
            $active.Add($shard)
            $next++
        }
        foreach ($shard in @($active.ToArray())) {
            if (!$shard.process.HasExited) { continue }
            $shard.process.WaitForExit()
            $shard.exit_code = $shard.process.ExitCode
            if ($shard.exit_code -ne 0) {
                Get-Content -LiteralPath $shard.stdout -Tail 25 | Write-Host
                Get-Content -LiteralPath $shard.stderr -Tail 25 | Write-Host
                throw "Axiom shard $($shard.index) failed with exit code $($shard.exit_code)."
            }
            if ((Get-FileHash -Algorithm SHA256 -LiteralPath $shard.source).Hash -ne $shard.sha256) {
                throw "Axiom shard source changed during checking: $($shard.source)"
            }
            $output = Get-Content -Raw -Encoding utf8 -LiteralPath $shard.stdout
            $reports = [regex]::Matches($output,
                "'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
            if ($reports.Count -ne $shard.names.Count) { throw "Incomplete axiom shard $($shard.index)." }
            for ($i = 0; $i -lt $reports.Count; $i++) {
                if ($reports[$i].Groups[1].Value -ne $shard.names[$i]) {
                    throw "Axiom declaration mismatch in shard $($shard.index)."
                }
                foreach ($axiom in ($reports[$i].Groups[2].Value -split ',')) {
                    if ($axiom.Trim() -and $axiom.Trim() -notin @('propext', 'Classical.choice', 'Quot.sound')) {
                        throw "Unapproved axiom: $axiom"
                    }
                }
            }
            $shard.reports = $reports.Count
            [void]$active.Remove($shard)
            $completed++
            Write-Host "PASS $Label axiom shard $completed/$($shards.Count) ($($shard.reports) reports)"
        }
        if ($active.Count) { [void]$active[0].process.WaitForExit(1000) }
    }
} finally {
    foreach ($shard in $active.ToArray()) {
        if (!$shard.process.HasExited) { Stop-Process -Id $shard.process.Id -Force }
    }
}
$combined = [System.Text.StringBuilder]::new()
foreach ($shard in $shards) {
    [void]$combined.Append([string](Get-Content -Raw -Encoding utf8 -LiteralPath $shard.stdout))
    [void]$combined.Append([string](Get-Content -Raw -Encoding utf8 -LiteralPath $shard.stderr))
}
[System.IO.File]::WriteAllText($LogFile, $combined.ToString(), [System.Text.UTF8Encoding]::new($false))
$manifestPath = Join-Path $shardDirectory 'manifest.json'
@($shards | Select-Object index, source, sha256, stdout, stderr, names, exit_code, reports) |
    ConvertTo-Json -Depth 8 | Set-Content -Encoding utf8 -LiteralPath $manifestPath
[pscustomobject]@{exit_code = 0; reports = $prints.Count; shard_count = $shards.Count; manifest = $manifestPath}
