import {publicUrl} from './public-reader.js';
export const esc = value => String(value ?? '').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));

export function highlight(source,start=1){
  let depth=0,inString=false;
  const keywords=new Set('def theorem lemma abbrev structure class inductive instance axiom opaque noncomputable namespace section end import open scoped variable universe by exact apply intro intros rintro rcases obtain constructor refine have let show change calc simp simpa rw rfl fun forall return with where if then else match classical aesop cases induction choose use specialize suffices set_option attribute include omit'.split(' '));
  return source.split('\n').map((line,index)=>{
    let out='',i=0;
    while(i<line.length){
      if(depth){let end=i;while(end<line.length){if(line.startsWith('/-',end)){depth++;end+=2;}else if(line.startsWith('-/',end)){depth--;end+=2;if(!depth)break;}else end++;}out+=`<span class="tok-comment">${esc(line.slice(i,end))}</span>`;i=end;continue;}
      if(line.startsWith('/-',i)){depth=1;out+='<span class="tok-comment">/-</span>';i+=2;continue;}
      if(line.startsWith('--',i)){out+=`<span class="tok-comment">${esc(line.slice(i))}</span>`;break;}
      if(inString||line[i]==='"'){let end=i+(inString?0:1);inString=true;while(end<line.length){if(line[end]==='\\')end+=2;else if(line[end++]==='"'){inString=false;break;}}out+=`<span class="tok-string">${esc(line.slice(i,end))}</span>`;i=end;continue;}
      const word=line.slice(i).match(/^[\p{L}_][\p{L}\p{N}_'.]*/u);
      if(word){const token=word[0],klass=keywords.has(token)?'tok-key':/^[A-Zℝℂℕ𝕜]/u.test(token)?'tok-type':'';out+=klass?`<span class="${klass}">${esc(token)}</span>`:esc(token);i+=token.length;continue;}
      out+=esc(line[i++]);
    }
    return `<span class="code-line"><span class="line-number" aria-hidden="true">${start+index}</span>${out||' '}</span>`;
  }).join('');
}

export function sourceHTML(declaration,module,{proof=false,hasProof=false,standalone=false}={}){
  let source=declaration.code;
  const isProof=['lemma','theorem'].includes(declaration.kind);
  if(isProof&&!proof&&!standalone)source=declaration.signature||source;
  const status=declaration.status;
  const label=status==='statement'?(hasProof?'Formal statement':'Proposition definition'):status==='proof'?'Proof present in source':status==='placeholder'?'Incomplete proof':status==='axiom'?'Axiom':'Definition';
  const explanation=status==='statement'?(hasProof?'The completed proof is shown under Proof. See Verification for the checks.':'This declaration specifies a proposition; it is not a proof.'):status==='proof'?'The displayed hypotheses remain part of this result.'+(standalone?'':' See Verification for build evidence.'):status==='placeholder'?'This source contains sorry or admit.':status==='axiom'?'This declaration assumes its conclusion.':'';
  const comment=esc(declaration.doc||'').replace(/\*\*([^*]+)\*\*/g,'<strong>$1</strong>').replace(/`([^`]+)`/g,'<code>$1</code>');
  return `<p class="status-line ${isProof?'proof':status}"><span>${label}.</span> ${explanation}</p>
    <div class="source-meta"><span>${esc(module.path)}:${declaration.line}</span><a target="_blank" rel="noopener" href="${publicUrl('/source?path='+encodeURIComponent(module.path))}">Source ↗</a></div>
    <pre class="lean-code"><code>${highlight(source,declaration.line)}</code></pre>
    <div class="source-actions"><button data-copy-source="${esc(module.path)}" data-copy-decl="${esc(declaration.name)}">Copy declaration</button><button data-full-module="${esc(module.path)}">Full module</button></div>
    ${comment?`<details class="context-details"><summary>Source notes</summary><div class="lean-comment">${comment}</div></details>`:''}
    <details class="context-details"><summary>Imports &amp; surrounding commands</summary><p class="selected-note">Read the full module for exact namespace and section scope.</p><pre class="lean-code">${highlight(declaration.context||'-- No preceding commands.')}</pre></details>`;
}

export function verificationHTML(evidence,result,{correspondenceShown=false}={}){
  const record=evidence.record;
  const facts=rows=>`<dl class="verification-facts">${rows.map(([label,value])=>`<div><dt>${esc(label)}</dt><dd>${esc(value)}</dd></div>`).join('')}</dl>`;
  if(!record){
    if(result.link?.scope==='discussion')return `<div class="verification"><h3>Correspondence with the formalisation</h3><p>${esc(result.link.note)}</p><p>No theorem certificate is attached to this passage.</p></div>`;
    return `<div class="verification"><div class="verification-state"><h3>Awaiting verification</h3><p>No verification record is attached to ${esc(result.type+' '+result.number)} yet. The Lean proofs can already be read here. The fresh kernel certificate will be attached when the separate verification run has finished and its correspondence has been checked.</p></div>
      ${facts([['Checked declaration','Not attached'],['Build result','Not recorded'],['Lean toolchain',evidence.toolchain],['Source hash','Awaiting a checked snapshot']])}
      <section class="verification-slot"><h3>Lean verification report</h3><p>The verification command, its status and the compiler report will appear here when a verification record is added.</p></section>
      <section class="verification-slot"><h3>Axioms &amp; remaining assumptions</h3><p>Space for the declaration’s axiom report, proof obligations and any additional hypotheses.</p></section>
      <section class="verification-slot"><h3>Certificate &amp; reproducibility</h3><p>Space for the certificate identifier, checked source hashes, Lean and mathlib versions, and the time of the run.</p></section>
      ${evidence.projectAuditAvailable?'<details class="context-details"><summary>Existing project audit (not a certificate for this result)</summary><button class="load-audit">Read project audit</button><div class="project-audit"></div></details>':''}</div>`;
  }
  if(record.schemaVersion===3){
    const checked=evidence.kernelVerified;
    const scope=record.scope==='complete'?'Complete result':record.scope==='definition'?'Definition':'Related result';
    const artifacts=record.artifacts.map(a=>`<li><a target="_blank" rel="noopener" href="${publicUrl('/verification-file?paper='+encodeURIComponent(evidence.paperId)+'&path='+encodeURIComponent(a.path))}">${esc(a.label)} ↗</a></li>`).join('');
    const axiomRows=Object.entries(record.axioms||{});
    return `<div class="verification"><div class="verification-state"><h3>${checked?'Kernel checked':'Verification record needs review'}</h3><p>${checked?'The completed fresh replay includes the declarations shown here. Their current Lean sources, the paper correspondence and the saved reports agree with the record.':'The current sources, paper correspondence or saved reports differ from this record. This badge cannot certify the displayed version.'}</p></div>
      ${facts([['Correspondence',scope],['Checked declarations',record.declarations.join('\n')],['Completed at',record.checkedAt],['Lean',record.leanVersion],['Certificate',record.certificateId]])}
      <section class="verification-slot"><h3>Scope of the result</h3><p>${esc(result.link.note)}</p><p>The hypotheses in the formal statement remain part of the theorem. A kernel check verifies the formal proposition; its correspondence with this edition is explained separately above.</p></section>
      <section class="verification-slot"><h3>The fresh kernel replay</h3><p>The completed run replayed ${Number(record.declarationsRechecked).toLocaleString()} declarations from ${Number(record.modules).toLocaleString()} imported modules, including mathlib and the Lean libraries, in an initially empty kernel environment. No declarations were skipped. Constructors and recursors generated by the kernel were compared with the saved declarations; unsafe and partial program declarations were included.</p><p>A deliberately corrupted proof was rejected. The run checked its frozen files before and after replay. This reader attaches that completed run and compares the sources and reports; it has not repeated the kernel replay.</p>${record.recoveryNote?'<details class="context-details"><summary>Completion of the PFP report</summary><p>'+esc(record.recoveryNote)+'</p></details>':''}</section>
      <section class="verification-slot"><h3>Axioms</h3>${axiomRows.length?'<p>The attached per-declaration audit records:</p><pre class="audit-code">'+esc(axiomRows.map(([n,a])=>n+'\n'+(a.join(', ')||'No axioms')).join('\n\n'))+'</pre>':'<p>This declaration is included in the kernel replay. A separate axiom list for it is not attached here; the full project reports are available below.</p>'}<p>Axioms remain assumptions. The imported runtime contains additional axioms; inclusion in the replay does not make those assumptions dependencies of the mathematical theorems.</p></section>
      <details class="context-details"><summary>Certificate, reports and source hashes</summary><p>The saved proof objects and replay scripts are in <code>${esc(record.originalBundle)}</code>. The reports below identify the run and its frozen files. SHA256 records establish file agreement; they are not digital signatures.</p><p>Reproduction command in that bundle:</p><pre class="audit-code">${esc(record.replayCommand)}</pre><ul>${artifacts}</ul>${evidence.changedSources?.length?'<p>Changed sources:</p><pre>'+esc(evidence.changedSources.join('\n'))+'</pre>':''}</details></div>`;
  }
  if(record.schemaVersion===2){
    const checked=evidence.kernelVerified;
    const scope=record.scope==='complete'?'Complete theorem':record.scope==='definition'?'Definition checked':'Supporting result checked';
    const artifacts=(record.artifacts||[]).map(a=>`<li><a target="_blank" rel="noopener" href="${publicUrl('/verification-file?paper='+encodeURIComponent(evidence.paperId||'jlms')+'&path='+encodeURIComponent(a.path))}">${esc(a.label||a.path.split('/').at(-1))} ↗</a></li>`).join('');
    return `<div class="verification"><div class="verification-state"><h3>${checked?'Kernel checked':'Verification record needs review'}</h3><p>${checked?esc(scope)+'. The clean compilation and fresh kernel replay both succeeded.':'The current passage, Lean sources or saved evidence no longer agree with this record. A new check is required.'}</p></div>
      ${facts([['Correspondence',scope],['Checked declarations',(record.declarations||[]).join('\n')],['Checked at',record.checkedAt],['Lean',record.leanVersion],['Mathlib',record.mathlibRevision],['Run',record.certificateId]])}
      <section class="verification-slot"><h3>${correspondenceShown?'Scope of this verification':'What was proved'}</h3>${correspondenceShown?'<p>This record verifies the Lean declarations named above. Their relation to the printed result is described at the top of this pane.</p>':'<p>'+esc(result.link?.note||record.correspondence)+'</p>'}<p>${esc(record.assumptionsText)}</p></section>
      <section class="verification-slot"><h3>The fresh check</h3><p>All ${esc(record.leanSourceCount)} ${esc(evidence.paperLabel||'JLMS')} Lean source files were copied into a separate directory. ${esc(evidence.paperLabel||'JLMS')} was compiled without any previous compilation of the project. Then lean4checker replayed the full imported theory in an empty environment using Lean’s kernel.</p><p>The compilation reused the pinned libraries; their declarations were included in the fresh replay. The checker omits unsafe and partial program declarations. It uses Lean’s own kernel.</p>
      ${facts((record.stages||[]).map(s=>[({build:'Clean project build',axioms:'Axiom audit','checker-build':'Checker compilation','kernel-root':'Import wrapper',kernel:'Fresh kernel replay','reader-declarations':'Reader declaration checks'})[s.name]||s.name,s.exitCode===0?'Passed · '+Math.round(s.seconds)+' s':'Failed']))}</section>
      <section class="verification-slot"><h3>Axioms</h3><p>The original audit checked ${esc(record.auditedDeclarations)} named declarations. A further traversal checked all ${esc(record.fullProjectDeclarations)} ${esc(evidence.paperLabel||'JLMS')} declarations, including those generated by Lean. Only propext, Classical.choice and Quot.sound occurred; there was no sorryAx or additional mathematical axiom.</p><pre class="audit-code">${esc(record.axiomReport)}</pre></section>
      <details class="context-details"><summary>Elaborated declarations</summary><pre class="audit-code">${esc(record.elaboratedTypes)}</pre></details>
      <details class="context-details"><summary>Commands, logs and source hashes</summary><p>These are the saved records of this run. The reader compares the current ${esc(evidence.paperLabel||'JLMS')} sources, the paper edition, the declaration links and the report hashes before showing “Kernel checked”.</p><ul>${artifacts}</ul><pre class="audit-code">${esc((record.stages||[]).map(s=>s.command.join(' ')).join('\n\n'))}</pre></details></div>`;
  }
  const matched=evidence.sourceMatch&&evidence.recordIdMatches;
  const success=record.exitCode===0;
  return `<div class="verification"><div class="verification-state"><h3>${!matched?'Source differs from the record':success?'Successful run recorded':'Run requires attention'}</h3><p>${matched?'The source files named in this record match their recorded hashes.':'This record cannot be treated as evidence for the currently displayed source.'} The reader has not rerun the command.</p></div>
    ${facts([['Checked declaration',record.declaration||'Not specified'],['Result',record.proofStatus||'Not specified'],['Exit status',record.exitCode??'Not specified'],['Checked at',record.checkedAt||'Not specified'],['Lean',record.leanVersion||'Not specified'],['Mathlib',record.mathlibRevision||'Not specified'],['Certificate',record.certificateId||'Not attached']])}
    <section class="verification-slot"><h3>Verification command &amp; report</h3><pre class="audit-code">${esc(Array.isArray(record.command)?record.command.join(' '):record.command||'')}${record.output?'\n\n'+esc(record.output):''}</pre></section>
    <section class="verification-slot"><h3>Axiom report</h3><pre class="audit-code">${esc(record.axiomReport||'No axiom report attached.')}</pre></section>
    <section class="verification-slot"><h3>Remaining assumptions</h3><p>${esc(Array.isArray(record.assumptions)?(record.assumptions.join('; ')||'The record lists no remaining assumptions. This has not been independently checked.'):'Not recorded.')}</p></section>
    <details class="context-details"><summary>Checked source hashes</summary><pre class="audit-code">${esc((record.sourceFiles||[]).map(f=>`${f.path}\n${f.sha256}`).join('\n\n'))}</pre></details></div>`;
}
