import {publicUrl} from './public-reader.js';
import {esc,highlight,sourceHTML,verificationHTML} from './lean-view.js';
import {createReadingContext} from './reading-context.js';
import {createPaperFollower} from './paper-follow.js';
const $=id=>document.getElementById(id);
const requestedPaper=new URLSearchParams(location.hash.slice(1)).get('paper');
const paperId=['jlms','pems','sigma','pfp','upfp','lpck','posets','jfa'].includes(requestedPaper)?requestedPaper:'jlms';
const api=name=>'/api/'+name+'?paper='+paperId;
const leanPath=link=>link.path||article.project+'/'+link.file;
const companion=$('lean-template').content.firstElementChild.cloneNode(true);
$('lean-side').append(companion);
const q=selector=>companion.querySelector(selector);
const panel=name=>q(`[data-panel="${name}"]`);
for(const tab of companion.querySelectorAll('[data-tab]')){
  const name=tab.dataset.tab;
  tab.id='lean-tab-'+name;tab.setAttribute('aria-controls','lean-panel-'+name);
  tab.tabIndex=name==='statement'?0:-1;
  panel(name).id='lean-panel-'+name;panel(name).setAttribute('aria-labelledby',tab.id);
}
const moduleCache=new Map();
let article,catalog,result,selectedDeclaration,selectedModule,mode='paper',requestVersion=0,toastTimer,citationKeys;
let symbols=new Map(),pendingMath=Promise.resolve(),readingContext,paperFollower,readingReady=false,readingPassage=null;
let companionView='formal',selectedTab='statement';
let savedPaperPassage=null,pendingPaperPassage=null;

async function get(url){const r=await fetch(publicUrl(url),{cache:'no-cache'});if(!r.ok)throw Error(`Could not read ${url} (${r.status})`);return r.json();}
function toast(text){$('toast').textContent=text;$('toast').classList.add('visible');clearTimeout(toastTimer);toastTimer=setTimeout(()=>$('toast').classList.remove('visible'),4000);}
function typeset(element){pendingMath=pendingMath.catch(()=>{}).then(async()=>{
  await window.mathReady;
  if(element.id==='paper'&&article?.paperId!=='jlms'){
    // Long papers contain thousands of formulae. Yield between small groups
    // so opening the article does not freeze the reader's controls.
    const formulae=[...element.querySelectorAll('.math')];element.setAttribute('aria-busy','true');
    try{for(let i=0;i<formulae.length;i+=100){await MathJax.typesetPromise(formulae.slice(i,i+100));await new Promise(resolve=>setTimeout(resolve,0));}}
    finally{element.removeAttribute('aria-busy');}
  }else await MathJax.typesetPromise([element]);
  // Resolving a TeX cross-reference can rebuild a formula elsewhere in the
  // paper. Restore its reminder as well as those in the current passage.
  readingContext?.activateFormulaReferences(document);
});return pendingMath;}
function indexSources(){symbols=new Map();for(const m of catalog.modules)for(const d of m.declarations){const name=d.name.split('.').at(-1);if(!symbols.has(name))symbols.set(name,[]);symbols.get(name).push({...d,path:m.path});}}
async function loadModule(path){if(!moduleCache.has(path))moduleCache.set(path,await get('/api/module?path='+encodeURIComponent(path)));return moduleCache.get(path);}
function remember(replace=false){const hash=new URLSearchParams({paper:paperId,mode});if(result)hash.set('result',result.id);if(mode==='lean')hash.set('tab',selectedTab);if(mode==='split'&&readingPassage&&readingPassage!==result?.id&&!readingContext?.activeId)hash.set('passage',readingPassage);if(mode==='split'&&readingContext?.activeId){hash.set('reference',readingContext.activeId);if(readingContext.detailTopic)hash.set('explain',readingContext.detailTopic);}history[replace?'replaceState':'pushState'](null,'','#'+hash);}
function restoreRoutePassage(route){
  if(!result)return;
  const proof=document.getElementById(route.get('passage')||'');
  const isProof=proof?.classList.contains('paper-proof')&&proof.dataset.proofOf===result.id;
  readingPassage=isProof?proof.id:result.id;
  if(isProof&&!route.has('tab'))showTab('proof');
  if(mode==='lean'){pendingPaperPassage=readingPassage;return;}
  jump(readingPassage,{instant:true});
}
function openParents(element){for(let node=element;node&&node!==$('paper-scroll');node=node.parentElement)if(node.tagName==='DETAILS')node.open=true;}
function jump(id,{instant=false}={}){
  if(mode==='lean')setMode('paper',{load:false,history:false});
  const element=document.getElementById(id);if(!element)return;
  paperFollower?.navigate(element);
  openParents(element);
  if(element.classList.contains('paper-result')){element.classList.remove('is-folded');element.querySelector('.result-body').hidden=false;element.querySelector('.fold-result').setAttribute('aria-expanded','true');}
  const scroller=$('paper-scroll');const position=element.getBoundingClientRect().top-scroller.getBoundingClientRect().top+scroller.scrollTop-32;
  scroller.scrollTo({top:Math.max(0,position),behavior:instant||matchMedia('(prefers-reduced-motion: reduce)').matches?'instant':'smooth'});
  element.classList.remove('flash-target');requestAnimationFrame(()=>element.classList.add('flash-target'));
  if(innerWidth<1000){$('contents').hidden=true;$('contents-button').setAttribute('aria-expanded','false');}
}
function configureCompanion(view){
  companionView=view;companion.dataset.view=view;
  const tabbed=['formal','related','definition'].includes(view);
  q('.lean-tabs').hidden=!tabbed;q('.correspondence').hidden=!tabbed||view==='related';
  q('.correspondence-kind').hidden=view!=='related';
  q('.formal-correspondence').hidden=view!=='related';
  q('.lean-wordmark span').textContent=view==='note'?'Notes':view==='source'?'Source':'Formalisation';
  for(const tab of companion.querySelectorAll('[data-tab]'))tab.hidden=!tabbed||(view==='definition'&&tab.dataset.tab==='proof');
  q('[data-tab="statement"]').textContent=view==='definition'?'Definition':view==='related'?'Related statement':'Statement';
  q('.lean-tabs').setAttribute('aria-label',view==='related'?'Related formalisation and its verification':'Formalisation and evidence');
  panel('statement').setAttribute('role',view==='source'?'region':'tabpanel');
  panel('statement').setAttribute('aria-labelledby',view==='source'?'lean-passage-title':'lean-tab-statement');
}
function showTab(name){
  // Notes have no tabs. Retain the reader's choice for the next formal result.
  const available=[...companion.querySelectorAll('[data-tab]')].filter(t=>!t.hidden);
  const activePanel=companionView==='note'?'note':companionView==='source'?'statement':available.some(t=>t.dataset.tab===name)?name:'statement';
  if(available.length)selectedTab=activePanel;
  for(const tab of companion.querySelectorAll('[data-tab]')){const selected=!tab.hidden&&tab.dataset.tab===activePanel;tab.setAttribute('aria-selected',String(selected));tab.tabIndex=selected?0:-1;}
  for(const body of companion.querySelectorAll('[data-panel]'))body.hidden=body.dataset.panel!==activePanel;
  q('.lean-tab-body').scrollTop=0;
}
function setMode(next,{history=true,load=true,anchor=null}={}){
  const previous=mode;
  const passage=next!==mode&&mode!=='lean'?(anchor||readingContext?.capturePassage()):null;
  const pinned=article?.results.find(r=>r.id===readingContext?.activeId);
  const hereBefore=readingReady&&mode!=='lean'&&paperFollower?.enabled?paperFollower.current():null;
  if(next==='lean'&&previous!=='lean'){savedPaperPassage=passage;pendingPaperPassage=null;}
  if(next!=='split')readingContext?.hidePinned();
  mode=next;document.body.classList.toggle('split',mode==='split');document.body.classList.toggle('lean-only',mode==='lean');
  $('paper-column').hidden=mode==='lean';$('lean-side').hidden=mode==='paper';$('split-divider').hidden=mode!=='split';
  for(const value of ['paper','split','lean'])$(value+'-mode').setAttribute('aria-pressed',String(mode===value));
  q('.lean-result-nav').hidden=mode!=='lean';q('.follow-paper').hidden=mode==='lean';q('.close-lean').hidden=mode==='lean';
  $('fold-proofs').hidden=$('fold-sections').hidden=mode==='lean';
  $('toc-list').hidden=mode==='lean';$('lean-toc-list').hidden=mode!=='lean';$('contents').querySelector('.contents-foot').hidden=mode==='lean';
  $('contents').querySelector('.contents-head > span').textContent=mode==='lean'?'Results':'Contents';
  $('contents-button').textContent=mode==='lean'?'Results':'Contents';$('contents-button').setAttribute('aria-label',mode==='lean'?'Choose a result':'Table of contents');
  if(mode!=='paper'&&!result)result=article?.results.find(r=>r.id===hereBefore?.id)||article?.results.find(r=>article.links[r.id]?.scope==='complete')||article?.results[0];
  if(previous==='lean'&&mode!=='lean'){
    paperFollower?.hold();
    if(pendingPaperPassage){jump(pendingPaperPassage,{instant:true});pendingPaperPassage=null;}
    else if(savedPaperPassage)readingContext.restorePassage(savedPaperPassage);
    savedPaperPassage=null;scheduleRunningHead();
  }else if(mode!=='lean'&&passage)readingContext.restorePassage(passage);
  if(mode==='lean'&&load){
    const chosen=pinned||(previous==='paper'?article.results.find(r=>r.id===hereBefore?.id):null)||result;
    if(chosen&&(companion.dataset.result!==chosen.id||pinned))inspect(chosen.id,{present:false,history:false,tab:pinned?'statement':selectedTab});
  }else if(mode==='split'&&load&&previous!=='lean'){
    const here=readingReady&&paperFollower?.enabled?paperFollower.current():null;
    inspect(here?.id||result.id,{present:false,history:false,tab:here?.part||'statement',passageId:here?.anchor});
  }
  updateResultNavigation();
  if(history)remember();
}
function presentCompanion(anchor=null){if(mode==='paper')setMode('split',{history:false,load:false,anchor});}
function renderResultNavigation(){
  const sections=new Map();
  for(const r of article.results){const section=r.number.split('.')[0];if(!sections.has(section))sections.set(section,[]);sections.get(section).push(r);}
  q('#lean-result-select').innerHTML=[...sections].map(([section,results])=>`<optgroup label="Section ${esc(section)}">${results.map(r=>`<option value="${esc(r.id)}">${esc(r.type+' '+r.number)}</option>`).join('')}</optgroup>`).join('');
  $('lean-toc-list').innerHTML=[...sections].map(([section,results])=>`<section class="lean-toc-section"><h3>Section ${esc(section)}</h3>${results.map(r=>`<button class="toc-link" data-lean-result="${esc(r.id)}">${esc(r.type+' '+r.number)}<span>${article.links[r.id]?.scope==='supporting'?'Related result':article.links[r.id]?.scope==='discussion'?'Note':''}</span></button>`).join('')}</section>`).join('');
  updateResultNavigation();
}
function updateResultNavigation(){
  if(!article)return;
  const index=article.results.findIndex(r=>r.id===result?.id);
  q('#lean-result-select').value=result?.id||'';
  q('.previous-result').disabled=index<=0;q('.next-result').disabled=index<0||index===article.results.length-1;
  for(const button of $('lean-toc-list').querySelectorAll('[data-lean-result]')){const current=button.dataset.leanResult===result?.id;button.classList.toggle('active',current);if(current)button.setAttribute('aria-current','true');else button.removeAttribute('aria-current');}
}
function chooseLeanResult(id){pendingPaperPassage=id;inspect(id,{present:false,tab:selectedTab});toggleContents(false);}
function choicesHTML(choices){return choices.map(d=>`<button class="proof-choice" data-proof-path="${esc(d.path)}" data-proof-name="${esc(d.name)}"><strong>${esc(d.label||d.name)}</strong><span>${esc(d.name)} · ${esc(d.path)}</span></button>`).join('');}
function proofPickerHTML(choices,selected){return '<label class="proof-picker">Part of the formal argument<select aria-label="Choose a proof" data-choose-proof>'+choices.map((d,i)=>`<option value="${i}" data-proof-path="${esc(d.path)}" data-proof-name="${esc(d.name)}"${d.name===selected?' selected':''}>${esc(d.label||d.name)}</option>`).join('')+'</select></label>';}
function renderReadingNotes(){
  for(const note of article.editionManifest?.readingNotes||[]){
    const passage=article.results.find(r=>r.id===note.resultId);
    const footer=$(note.resultId)?.querySelector('.result-footer');
    if(!passage||!footer)throw Error('Missing passage for reading note: '+note.resultId);
    const html=`<details class="edition-correction"><summary>${esc(note.title)}</summary>${note.html}<p><button class="reading-note-proof" data-inspect="${esc(note.resultId)}" data-inspect-tab="proof">${esc(note.proofLabel)}</button></p></details>`;
    footer.insertAdjacentHTML('beforebegin',html);
    passage.statementHtml+=html;
  }
}
async function inspect(id,{present=true,history=true,trigger=null,tab='statement',automatic=false,passageId=null}={}){
  const r=article.results.find(x=>x.id===id);if(!r)return;result=r;const version=++requestVersion;
  readingPassage=passageId;
  if(!automatic)paperFollower?.hold();
  companion.dataset.result=id;
  updateResultNavigation();
  const heading=trigger?.closest('#paper .result-heading')||trigger?.closest('#paper .reading-note-proof');
  const anchor=heading?{element:heading,offset:heading.getBoundingClientRect().top}:null;
  readingContext?.hidePinned();
  for(const el of document.querySelectorAll('.paper-result'))el.classList.toggle('selected',el.id===id);
  q('.selected-name').textContent=r.type+' '+r.number;q('.paper-statement-preview').innerHTML=r.statementHtml;q('.paper-statement-preview').hidden=false;
  const link=article.links[id];q('.selected-note').textContent=link?.note||(link?'The formal statement, supporting proof code and verification evidence.':'A space for the Lean statement, proof and verification record for this result.');
  configureCompanion(!link?.file?'note':link.scope==='definition'?'definition':link.scope==='supporting'?'related':'formal');
  q('.formal-correspondence p').textContent=link?.note||'';
  q('.correspondence summary').textContent=link?.relation==='related'?'Related development · correspondence':'Correspondence with the paper';
  for(const name of ['statement','proof','verification'])panel(name).innerHTML=link?.file?'<p class="selected-note">Reading the current source…</p>':'';
  panel('note').innerHTML=link?.file?'':'<p class="passage-note-label">In the formalisation</p><p>'+esc(link?.note||'No corresponding declaration has been identified.')+'</p>';
  showTab(tab);if(present)presentCompanion(anchor);if(history)remember();
  typeset(q('.paper-statement-preview'));
  try{
    if(link?.file){
      const m=await loadModule(leanPath(link));if(version!==requestVersion)return;
      const d=m.declarations.find(x=>x.name===link.declaration);if(!d)throw Error(`The linked declaration ${link.declaration} is no longer in ${link.file}. Refresh Lean to reread the project.`);
      renderDeclaration(d,m);
      const proofs=(link.proofs||[]).map(p=>({...p,path:leanPath(p),name:p.declaration}));
      if(proofs.length){
        const pm=await loadModule(proofs[0].path);if(version!==requestVersion)return;
        const pd=pm.declarations.find(x=>x.name===proofs[0].name);
        if(!pd)throw Error('A linked proof could not be found. Refresh Lean to reread the project.');
        panel('proof').innerHTML=(proofs.length>2?proofPickerHTML(proofs,pd.name):proofs.length>1?'<div class="proof-choices"><h3>Parts of the formal argument</h3>'+choicesHTML(proofs)+'</div>':'')+sourceHTML(pd,pm,{proof:true});
      }else if(['theorem','lemma'].includes(d.kind)){
        panel('proof').innerHTML=sourceHTML(d,m,{proof:true});
      }else{
        panel('proof').innerHTML='';
        configureCompanion('definition');showTab(tab);
      }
    }else{
      selectedDeclaration=selectedModule=null;
      return;
    }
    const evidence=await get(api('evidence')+'&result='+encodeURIComponent(id));if(version!==requestVersion)return;panel('verification').innerHTML=verificationHTML(evidence,{...r,link},{correspondenceShown:link.scope==='supporting'});
  }catch(error){if(version===requestVersion){panel('statement').innerHTML=`<div class="empty-lean"><h3>Source unavailable</h3><p>${esc(error.message)}</p></div>`;toast(error.message);}}
}
function renderDeclaration(d,m,{breadcrumb=false}={}){
  selectedDeclaration=d;selectedModule=m;
  if(breadcrumb){configureCompanion('source');q('.selected-name').textContent=d.name;}
  panel('statement').innerHTML=(breadcrumb?`<button class="source-breadcrumb" data-return-result>‹ Back to ${esc(result.type+' '+result.number)}</button>`:'')+sourceHTML(d,m,{hasProof:!breadcrumb&&!!article.links[result.id]?.proofs?.length,standalone:breadcrumb});
  const deps=[];const seen=new Set();
  for(const token of new Set(d.code.match(/[\p{L}_][\p{L}\p{N}_'.]*/gu)||[])){
    if(token===d.name)continue;const options=symbols.get(token.split('.').at(-1))||[];const found=options.find(x=>x.path.startsWith(article.project+'/'))||options[0];
    if(found&&!(found.path===m.path&&found.name===d.name)&&!seen.has(found.path+'#'+found.name)){seen.add(found.path+'#'+found.name);deps.push(found);}
  }
  if(deps.length)panel('statement').insertAdjacentHTML('beforeend','<section class="dependencies"><h3>Definitions used here</h3><div class="dependency-list">'+deps.slice(0,24).map(x=>`<button data-definition-path="${esc(x.path)}" data-definition-name="${esc(x.name)}">${esc(x.name)}</button>`).join('')+'</div></section>');
  if(breadcrumb)q('.selected-note').textContent=d.name+' · '+m.path;
}
async function openDefinition(path,name){paperFollower?.pause();const version=requestVersion;try{const m=await loadModule(path),d=m.declarations.find(x=>x.name===name);if(version!==requestVersion)return;if(!d)throw Error('Declaration not found in the current source.');renderDeclaration(d,m,{breadcrumb:true});showTab('statement');}catch(e){toast(e.message);}}
async function openProof(path,name){const version=requestVersion;try{const m=await loadModule(path),d=m.declarations.find(x=>x.name===name);if(version!==requestVersion)return;if(!d)throw Error('Proof declaration not found.');const proofs=(article.links[result.id]?.proofs||[]).map(p=>({...p,path:leanPath(p),name:p.declaration}));panel('proof').innerHTML=(proofs.length>2?proofPickerHTML(proofs,name):`<button class="source-breadcrumb" data-return-proofs>‹ Proof declarations for ${esc(result.type+' '+result.number)}</button>`)+sourceHTML(d,m,{proof:true});showTab('proof');}catch(e){toast(e.message);}}
function sourceSearch(){
  const query=$('source-search').value.toLowerCase();const matches=catalog.modules.flatMap(m=>m.declarations.filter(d=>(m.path+' '+d.name).toLowerCase().includes(query)).map(d=>({...d,path:m.path})));
  $('source-results').innerHTML=matches.slice(0,100).map(d=>`<button class="source-result" data-library-path="${esc(d.path)}" data-library-name="${esc(d.name)}"><strong>${esc(d.name)}</strong><span>${esc(d.path)}:${d.line} · ${esc(d.kind)}</span></button>`).join('')+(matches.length>100?'<p class="selected-note">Type more to narrow the results.</p>':'');
}
function showSourceSearch(){sourceSearch();$('source-dialog').showModal();$('source-search').focus();}
function toggleContents(open){$('contents').hidden=!open;$('contents-button').setAttribute('aria-expanded',String(open));}
let sectionFrame=0,textSize=100;
function updateRunningHead(){
  sectionFrame=0;
  if(mode==='lean')return;
  const top=$('paper-scroll').getBoundingClientRect().top+80;
  let current=null;
  for(const section of document.querySelectorAll('#article-body > .paper-section')){
    if(section.getBoundingClientRect().top>top)break;
    current=section;
  }
  const number=current?.querySelector(':scope > summary .section-number')?.innerText.replace(/\.$/,'');
  const title=current?.querySelector(':scope > summary h2')?.innerText;
  const label=title?(number?'§ '+number+' · ':'')+title:'Title & abstract';
  $('current-section').textContent=label;$('current-section').title=label;
  for(const link of $('contents').querySelectorAll('[data-target]')){
    const active=link.dataset.target===(current?.id||'top');
    link.classList.toggle('active',active);
    if(active)link.setAttribute('aria-current','location');else link.removeAttribute('aria-current');
  }
}
function scheduleRunningHead(){if(!sectionFrame)sectionFrame=requestAnimationFrame(updateRunningHead);}
function changeTextSize(amount){
  const passage=readingContext?.capturePassage();
  textSize=Math.max(90,Math.min(125,textSize+amount));
  document.documentElement.style.setProperty('--type-scale',textSize/100);
  $('text-smaller').disabled=textSize===90;$('text-larger').disabled=textSize===125;
  document.querySelector('.type-controls').setAttribute('aria-label','Text size: '+textSize+'%');
  if(passage)readingContext.restorePassage(passage);
  scheduleRunningHead();
}
function showCitation(keys){readingContext?.hidePreview();citationKeys=keys.split(',').map(x=>x.trim());$('citation-content').innerHTML=citationKeys.map(key=>{const r=article.references.find(x=>x.key===key);return r?`<p><strong>[${r.number}]</strong> ${r.html}</p>`:'';}).join('');$('citation-dialog').showModal();typeset($('citation-content'));}

document.addEventListener('click',async event=>{
  const button=event.target.closest('button,a');if(!button)return;
  if(button.dataset.leanResult){chooseLeanResult(button.dataset.leanResult);return;}
  if(button.dataset.inspect){inspect(button.dataset.inspect,{trigger:button,tab:button.dataset.inspectTab||'statement'});return;}
  if(button.classList.contains('cross-ref')&&button.dataset.readingRef){event.preventDefault();readingContext.pin(button.dataset.readingRef,button,{focus:event.detail===0});return;}
  if(button.classList.contains('fold-result')){const block=button.closest('.paper-result');const folded=!block.classList.contains('is-folded');block.classList.toggle('is-folded',folded);block.querySelector('.result-body').hidden=folded;button.setAttribute('aria-expanded',String(!folded));button.setAttribute('aria-label',(folded?'Expand ':'Fold ')+block.querySelector('.result-name').textContent.replace(/\.$/,''));return;}
  if(button.dataset.target){event.preventDefault();if(button.closest('dialog'))button.closest('dialog').close();jump(button.dataset.target);return;}
  if(button.dataset.cite){showCitation(button.dataset.cite);return;}
  if(button.hasAttribute('data-close-dialog')){button.closest('dialog').close();return;}
  if(button.dataset.tab){showTab(button.dataset.tab);if(mode==='lean')remember(true);return;}
  if(button.classList.contains('follow-paper')){paperFollower.enabled?paperFollower.pause():paperFollower.resume();return;}
  if(button.classList.contains('close-lean')){setMode('paper');return;}
  if(button.classList.contains('source-search-button')){showSourceSearch();return;}
  if(button.dataset.definitionPath){openDefinition(button.dataset.definitionPath,button.dataset.definitionName);return;}
  if(button.dataset.proofPath){openProof(button.dataset.proofPath,button.dataset.proofName);return;}
  if(button.dataset.libraryPath){$('source-dialog').close();if(!result)result=article.results.find(r=>article.links[r.id]?.scope==='complete')||article.results[0];presentCompanion();openDefinition(button.dataset.libraryPath,button.dataset.libraryName);return;}
  if(button.hasAttribute('data-return-result')){inspect(result.id,{present:false,history:false});return;}
  if(button.hasAttribute('data-return-proofs')){inspect(result.id,{present:false,history:false,tab:'proof'});return;}
  if(button.dataset.copySource){try{const m=await loadModule(button.dataset.copySource),d=m.declarations.find(x=>x.name===button.dataset.copyDecl);await navigator.clipboard.writeText(d.code);toast('Lean declaration copied.');}catch{toast('Clipboard access is unavailable. Select and copy the source text.');}return;}
  if(button.dataset.fullModule){paperFollower?.pause();const version=requestVersion,m=await loadModule(button.dataset.fullModule);if(version!==requestVersion)return;const container=button.closest('[data-panel]');container.innerHTML=`<button class="source-breadcrumb" data-return-result>‹ Return to the result</button><div class="source-meta">${esc(m.path)} · ${m.hash.slice(0,12)}</div><pre class="lean-code full-module">${highlight(m.source)}</pre>`;return;}
  if(button.classList.contains('load-audit')){button.disabled=true;const audit=await get(api('project-audit'));button.parentElement.querySelector('.project-audit').innerHTML='<p class="selected-note">Report for the project as a whole. No source-hash match to this selected result has been recorded.</p><pre class="audit-code">'+esc(audit.text)+'</pre>';return;}
  if(button.classList.contains('refresh-lean')){button.disabled=true;const activeTab=selectedTab;try{catalog=await get(api('catalog'));article.links=(await get(api('article'))).links;moduleCache.clear();indexSources();if(result)await inspect(result.id,{present:false,history:false,tab:activeTab});toast('Lean sources and verification records refreshed.');}catch(e){toast(e.message);}finally{button.disabled=false;}return;}
});
$('paper-mode').onclick=()=>setMode('paper');$('split-mode').onclick=()=>setMode('split');$('lean-mode').onclick=()=>setMode('lean');
companion.addEventListener('change',e=>{if(e.target.matches('[data-choose-proof]')){const option=e.target.selectedOptions[0];openProof(option.dataset.proofPath,option.dataset.proofName);}});
q('#lean-result-select').onchange=e=>chooseLeanResult(e.target.value);
q('.previous-result').onclick=()=>{const i=article.results.findIndex(r=>r.id===result?.id);if(i>0)chooseLeanResult(article.results[i-1].id);};
q('.next-result').onclick=()=>{const i=article.results.findIndex(r=>r.id===result?.id);if(i>=0&&i<article.results.length-1)chooseLeanResult(article.results[i+1].id);};
q('.show-in-paper').onclick=()=>{pendingPaperPassage=result?.id;setMode('split',{load:false});};
$('contents-button').onclick=()=>toggleContents($('contents').hidden);$('close-contents').onclick=()=>toggleContents(false);
$('current-section').onclick=()=>toggleContents($('contents').hidden);
$('text-smaller').onclick=()=>changeTextSize(-5);$('text-larger').onclick=()=>changeTextSize(5);
$('paper-scroll').addEventListener('scroll',scheduleRunningHead,{passive:true});
new ResizeObserver(scheduleRunningHead).observe($('paper'));
$('fold-proofs').onclick=()=>{const fold=$('fold-proofs').getAttribute('aria-pressed')!=='true';for(const p of document.querySelectorAll('#article-body .paper-proof'))p.open=!fold;$('fold-proofs').setAttribute('aria-pressed',String(fold));$('fold-proofs').textContent=fold?'Expand proofs':'Fold proofs';};
$('fold-sections').onclick=()=>{const fold=$('fold-sections').getAttribute('aria-pressed')!=='true';for(const s of document.querySelectorAll('#article-body .paper-section'))s.open=!fold;$('fold-sections').setAttribute('aria-pressed',String(fold));$('fold-sections').textContent=fold?'Expand sections':'Fold sections';};
$('source-search').oninput=sourceSearch;
$('about-button').onclick=$('edition-details').onclick=()=>$('about-dialog').showModal();
$('citation-jump').onclick=()=>{const ref=article.references.find(r=>r.key===citationKeys[0]);$('citation-dialog').close();if(ref)jump('reference-'+ref.number);};
document.querySelector('.journal-mark').onclick=e=>{e.preventDefault();jump('top');remember();};
companion.querySelector('.lean-tabs').addEventListener('keydown',e=>{if(['ArrowLeft','ArrowRight'].includes(e.key)){const tabs=[...companion.querySelectorAll('[data-tab]')].filter(t=>!t.hidden);if(!tabs.length)return;const i=tabs.indexOf(document.activeElement),next=(i+(e.key==='ArrowRight'?1:tabs.length-1))%tabs.length;e.preventDefault();tabs[next].focus();showTab(tabs[next].dataset.tab);if(mode==='lean')remember(true);}});
function resize(value){value=Math.max(35,Math.min(70,value));document.documentElement.style.setProperty('--split',value+'%');$('split-divider').setAttribute('aria-valuenow',Math.round(value));}
$('split-divider').addEventListener('pointerdown',e=>{const divider=$('split-divider');divider.setPointerCapture(e.pointerId);const drag=ev=>resize(ev.clientX/innerWidth*100);const end=()=>{divider.removeEventListener('pointermove',drag);divider.removeEventListener('pointerup',end);};divider.addEventListener('pointermove',drag);divider.addEventListener('pointerup',end);});
$('split-divider').addEventListener('keydown',e=>{if(['ArrowLeft','ArrowRight'].includes(e.key)){e.preventDefault();resize(Number($('split-divider').getAttribute('aria-valuenow'))+(e.key==='ArrowRight'?3:-3));}});
function restoreRoute(route){
  if((route.get('paper')||'jlms')!==paperId){location.reload();return;}
  result=article.results.find(r=>r.id===route.get('result'))||null;
  selectedTab=['statement','proof','verification'].includes(route.get('tab'))?route.get('tab'):'statement';
  setMode(['split','lean'].includes(route.get('mode'))?route.get('mode'):'paper',{history:false,load:false});
  if(result){inspect(result.id,{present:false,history:false,tab:selectedTab});restoreRoutePassage(route);}
  if(mode==='split'&&route.has('reference'))readingContext.pin(route.get('reference'),null,{history:false,detail:route.get('explain')});
}
window.addEventListener('popstate',()=>{if(article)restoreRoute(new URLSearchParams(location.hash.slice(1)));});
async function init(){
  try{
    article=await get(api('article'));catalog={papers:[],modules:[]};
    renderEdition();
    $('article-title').innerHTML=article.title;$('abstract-text').innerHTML=article.abstract;$('article-body').innerHTML=article.html;$('loading').hidden=true;
    renderReadingNotes();
    readingContext=createReadingContext({article,paper:$('paper'),side:$('lean-side'),typeset,jump,inspect,
      openSide:()=>setMode('split',{history:false,load:false}),closeSide:()=>setMode('paper'),
      showLean:()=>paperFollower?.enabled&&paperFollower.current()?paperFollower.resume():inspect(result?.id||article.results[0].id),selectPassage:id=>{result=article.results.find(r=>r.id===id)||result;},changed:(replace=false)=>remember(replace)});
    paperFollower=createPaperFollower({paper:$('paper'),scroller:$('paper-scroll'),
      isActive:()=>mode==='split'&&!readingContext.activeId&&!document.querySelector('dialog[open]'),
      onStateChange:following=>{const button=q('.follow-paper');button.setAttribute('aria-pressed',String(following));button.textContent=following?'Following paper':'Follow paper';button.title=following?'Pause following to keep this Lean passage here':'Show the formalisation of the passage you are reading';},
      onPassage:(passage,{force})=>{
        const activeTab=selectedTab;
        const tab=activeTab==='verification'?'verification':passage.part;
        if(!force&&companion.dataset.result===passage.id){readingPassage=passage.anchor;if(activeTab!==tab)showTab(tab);remember(true);return;}
        inspect(passage.id,{present:false,history:false,tab,automatic:true,passageId:passage.anchor});remember(true);
      }});
    $('toc-list').innerHTML=article.toc.map(s=>`<button class="toc-link ${s.level===2?'sub':''}" data-target="${s.id}"><span class="toc-number">${s.number}</span><span>${s.title.replace(/<\/?(?:a|button)\b[^>]*>/g,'')}</span></button>`).join('');
    renderResultNavigation();
    // Reading the paper does not depend on indexing the complete Lean library.
    get(api('catalog')).then(value=>{catalog=value;indexSources();}).catch(error=>toast(error.message));
    $('edition-source').textContent=article.edition+' '+article.inputs.length+' source files; edition hash '+article.sourceHash.slice(0,12)+'.';
    await typeset($('paper'));await typeset($('toc-list'));
    updateRunningHead();
    restoreRoute(new URLSearchParams(location.hash.slice(1)));
    readingReady=true;paperFollower.start();
    remember(true);
  }catch(error){$('loading').hidden=false;$('loading').textContent='The article could not open: '+error.message;toast(error.message);}
}
function renderEdition(){
  const edition=article.editionManifest;
  $('paper-select').value=paperId;
  $('paper-select').title=$('paper-select').selectedOptions[0].textContent;
  document.title=article.paperLabel+' · Paper and Lean';
  document.body.dataset.paper=paperId;
  document.querySelector('.author').textContent=article.author||'Antonio Acuaviva';
  q('.companion-footer span').textContent=article.paperLabel+' · Lean library';
  $('source-dialog').querySelector('h2').textContent=article.paperLabel+' Lean library';
  $('source-search').placeholder='Find a definition, theorem or module…';
  if(paperId!=='jlms'){
    document.querySelector('.affiliation').hidden=true;
    $('about-dialog').querySelector(':scope > p').textContent=edition.editionNote;
    $('about-dialog').querySelector(':scope > details').hidden=true;
    const original=$('about-dialog').querySelector('a[data-source-original]');
    original.href=publicUrl('/paper-source-original.zip?id='+paperId);original.download='arxiv-'+edition.arxivVersion+'.tar.gz';
    original.textContent='Original arXiv archive';
    const working=$('about-dialog').querySelector('a[data-source-author]');
    working.href=publicUrl('/paper-source.zip?id='+paperId);working.download=paperId+'-arxiv-source.zip';working.textContent='LaTeX source ZIP';
    working.parentElement.nextElementSibling.innerHTML='<a href="'+esc(edition.arxivUrl)+'" target="_blank" rel="noopener">View this version on arXiv ↗</a>';
    if(edition.corrections.length){const details=$('about-dialog').querySelector(':scope > details');details.hidden=false;details.innerHTML='<summary>Corrections in this reading edition</summary>'+edition.corrections.map(c=>'<p>'+esc(c.description)+'</p>').join('');}
  }
}
$('paper-select').onchange=e=>{location.hash=new URLSearchParams({paper:e.target.value,mode});location.reload();};
init();
