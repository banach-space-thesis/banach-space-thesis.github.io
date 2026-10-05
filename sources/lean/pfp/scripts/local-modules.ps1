# Shared local-project resolver. The PFP proof closure may use the separately
# built Posets, JFA and JLMS projects through explicit Lake path dependencies.
function Resolve-LocalLeanModule([string]$module) {
    $project = switch (($module -split '\.')[0]) {
        'PFP' { 'pfp' }
        'ThesisCommon' { 'common' }
        'Posets' { 'posets' }
        'PosetsCommon' { 'posets' }
        'JFA' { 'jfa' }
        'JLMS' { 'jlms' }
        default { return $null }
    }
    "$project/$($module.Replace('.','/')).lean"
}

function RemoveLeanComments([string]$source) {
    $result = [System.Text.StringBuilder]::new()
    $depth = 0
    for ($i=0; $i -lt $source.Length; $i++) {
        $pair = if ($i+1 -lt $source.Length) { $source.Substring($i,2) } else { '' }
        if ($pair -eq '/-') { $depth++; $i++; continue }
        if ($depth -gt 0) {
            if ($pair -eq '-/') { $depth--; $i++ }
            elseif ($source[$i] -eq "`n") { [void]$result.Append("`n") }
            continue
        }
        if ($pair -eq '--') {
            while ($i -lt $source.Length -and $source[$i] -ne "`n") { $i++ }
            [void]$result.Append("`n")
            continue
        }
        [void]$result.Append($source[$i])
    }
    $result.ToString()
}

function Get-VerificationInputSnapshot([string]$root) {
    $queue = [System.Collections.Generic.Queue[string]]::new()
    foreach ($module in @('PFP','PFP.Audit','ThesisCommon.PFPAudit','ThesisCommon.PFPAuditImports')) { $queue.Enqueue($module) }
    $seen = [System.Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
    $projects = [System.Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
    $records = [System.Collections.Generic.List[object]]::new()
    while ($queue.Count) {
        $module = $queue.Dequeue()
        if (!$seen.Add($module)) { continue }
        $relative = Resolve-LocalLeanModule $module
        if (!$relative) { continue }
        $path = Join-Path $root $relative
        $content = RemoveLeanComments (Get-Content -Raw -Encoding utf8 -LiteralPath $path)
        foreach ($match in [regex]::Matches($content,'(?m)^import ([A-Za-z0-9_.]+)')) { $queue.Enqueue($match.Groups[1].Value) }
        if ($content -match '(?m)^\s*(?:axiom|opaque)\s|\b(sorry|admit|native_decide)\b') { throw "Unapproved source construct: $relative" }
        $records.Add([ordered]@{kind='lean';path=$relative;sha256=(Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash})
        [void]$projects.Add(($relative -split '/')[0])
    }
    $configPaths = @('pfp/source-manifest.json','pfp/requested-scope.json','pfp/scripts/verify.ps1','pfp/scripts/update-records.ps1','pfp/scripts/local-modules.ps1','pfp/scripts/check-axiom-shards.ps1','pfp/scripts/check-paper-audit.ps1')
    if (@($seen | Where-Object { $_.StartsWith('ThesisCommon.FixedPoint.') }).Count) {
        $configPaths += @('common/ThesisCommon/FixedPoint/SOURCE.json','common/ThesisCommon/FixedPoint/LICENSE')
    }
    foreach ($p in $projects) {
        foreach ($file in @('lakefile.toml','lake-manifest.json','lean-toolchain')) { $configPaths += "$p/$file" }
    }
    foreach ($relative in $configPaths) {
        $records.Add([ordered]@{kind='configuration';path=$relative;sha256=(Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $root $relative)).Hash})
    }
    @($records | Sort-Object -Property path -CaseSensitive)
}

function Assert-VerificationSnapshotsEqual([object[]]$before, [object[]]$after) {
    $old = [System.Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
    foreach ($record in $before) { $old.Add($record.path,$record) }
    if ($before.Count -ne $after.Count) { throw 'Verification input closure changed during checking; publication cancelled.' }
    $afterSeen = [System.Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
    foreach ($record in $after) {
        if (!$afterSeen.Add($record.path) -or !$old.ContainsKey($record.path) -or $old[$record.path].kind -ne $record.kind -or $old[$record.path].sha256 -ne $record.sha256) {
            throw "Verification input changed during checking: $($record.path); publication cancelled."
        }
    }
}

function Assert-VerificationSnapshotFilesUnchanged([string]$root, [object[]]$records) {
    foreach ($record in $records) {
        $path = Join-Path $root $record.path
        if (!(Test-Path -LiteralPath $path) -or (Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash -ne $record.sha256) {
            throw "Verification input changed before publication: $($record.path); publication cancelled."
        }
    }
}
