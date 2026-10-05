import {esc} from './lean-view.js';
import {detailNotes as jlmsNotes,detailHTML as renderDetail} from './reader-details.js';
import {paperNotes,addPaperGlossary,paperNotation} from './paper-notes.js';
import {annotateFormula,activateFormulaReferences,addFormulaGlossary} from './formula-notes.js';

// These correspondences are deliberately explicit. In particular, the support
// of a neighbourhood family and the support of a functional are different.
export function createReadingContext({article, paper, side, typeset, openSide, closeSide, jump, inspect, showLean, selectPassage, changed}) {
  const entries=new Map(), results=new Map(article.results.map(r=>[r.id,r]));
  const words=[];
  const detailNotes=article.paperId==='jlms'?jlmsNotes:(paperNotes[article.paperId]||{});
  const detailHTML=(id,topic,escape)=>renderDetail(id,topic,escape,detailNotes);
  function resultPart(id){const r=results.get(id);if(!r)throw Error('Missing reading reference: '+id);return r.statementHtml;}
  function paragraph(id,prefix){
    const matches=[...paper.querySelectorAll('#article-body p')].filter(p=>p.textContent.trim().startsWith(prefix));
    if(matches.length!==1)throw Error('Ambiguous reading reference: '+id);
    matches[0].id=id;return matches[0];
  }
  function add(id,title,source,target,html,pattern,extras={}){
    const entry={id,title,source,target,html,...extras};entries.set(id,entry);
    if(pattern)words.push({id,pattern});return entry;
  }
  function definition(id,title,pattern,extras={}){
    const r=results.get(id);return add(id,title,`Definition ${r.number}`,id,r.statementHtml,pattern,{leanResult:id,...extras});
  }
  // A prose paragraph may introduce several concepts. Give each term its own
  // definition, explicitly restated, while keeping the original passage available.
  const tex=String.raw;
  function glossary(id,title,source,target,html,pattern,originalHtml,extras={}){
    return add(id,title,source+' · restated',target,html,pattern,{wordingLabel:'Definition',originalHtml,...extras});
  }
  if(article.paperId==='jlms'){
  const convention=paragraph('context-neighbourhood-convention','From now on, whenever we refer to a neighbourhood');
  const combined=paragraph('context-disjoint-neighbourhoods','Combining the previous definitions');
  // Match longer phrases before shorter ones, including the author's plural
  // variant and the phrase "collection of neighbourhoods" used in the proof.
  glossary('disjoint-neighbourhoods','Pairwise disjoint neighbourhood collection','Definitions 4.1–4.2 · §4',combined.id,
    tex`<p>A collection of compact, clopen sets assigned bijectively to the points of \(F\), with \(k\in U(k)\) for every \(k\in F\), and</p>\[U(k)\cap U(\ell)=\varnothing\quad\text{whenever }k\ne\ell.\]<p>Thus each point has its own neighbourhood, and those neighbourhoods do not overlap.</p>`,
    'pairwise\\s+disjoint\\s+(?:neighbourhoods?\\s+collections?|collections?\\s+of\\s+neighbourhoods)(?:\\s+around)?',
    resultPart('definition-4-1')+resultPart('definition-4-2')+combined.outerHTML+convention.outerHTML,
    {leanResult:'definition-4-2',related:['definition-4-1','definition-4-2','neighbourhoods']});
  definition('definition-4-2','Neighbourhood collection','neighbourhoods?\\s+collections?(?:\\s+around)?',
    {html:resultPart('definition-4-2')+'<div class="reading-convention"><h3>The convention in this paper</h3>'+convention.outerHTML+'</div>',related:['definition-4-1','neighbourhoods']});
  definition('definition-4-1','Pairwise disjoint','pairwise\\s+disjoint(?:ness)?', {related:['disjoint-neighbourhoods']});
  add('neighbourhoods','Neighbourhoods in this paper','Convention · §4',convention.id,convention.outerHTML,
    'neighbourhoods?',{related:['definition-4-2','disjoint-neighbourhoods']});
  definition('definition-4-3','Support of a neighbourhood collection',null,{
    html:tex`<p>\(S(\mathcal U)\) is the <em>support</em> of the neighbourhood collection: the region covered by its members.</p>\[S(\mathcal U)=\bigcup_{U\in\mathcal U}U.\]`,
    originalHtml:resultPart('definition-4-3'),wordingLabel:'Definition',related:['definition-4-2']});
  definition('definition-4-4','Finite and countable subsets','(?:finite|countable)\\s+subsets');
  definition('definition-4-6','The neighbourhood projection',null,{related:['disjoint-neighbourhoods','definition-4-10']});
  definition('definition-4-9','Support of a functional',null);
  definition('definition-4-10','Restriction operator','restriction\\s+operators?',{related:['definition-4-9']});
  definition('definition-5-1','Zero set and vanishing on a set','zero\\s+sets?|vanishes\\s+at\\s+a\\s+set');
  const norms=paragraph('context-algebra-norms','By an algebra norm');
  glossary('unique-complete-norm','Unique complete algebra norm','Definition · §1.1',norms.id,
    tex`<p>An algebra has a <em>unique complete algebra norm</em> if any two complete algebra norms on it are equivalent.</p><p>Equivalence means that each norm is bounded by a positive constant times the other; it does not require numerical equality.</p>`,
    'unique\\s+complete\\s+(?:algebra\\s+)?norms?',norms.outerHTML,{related:['unique-norm','algebra-norms']});
  glossary('unique-norm','Unique algebra norm','Definition · §1.1',norms.id,
    tex`<p>An algebra has a <em>unique algebra norm</em> if any two algebra norms on it are equivalent: for each pair \(p,q\), there are constants \(c,C>0\) such that</p>\[c\,p(a)\leq q(a)\leq C\,p(a)\quad\text{for every }a.\]<p>“Unique” means equivalent, not necessarily equal.</p>`,
    'unique\\s+(?:algebra\\s+)?norms?',norms.outerHTML,{related:['algebra-norms','unique-complete-norm']});
  glossary('algebra-norms','Algebra norm','Definition · §1.1',norms.id,
    tex`<p>An <em>algebra norm</em> is a vector-space norm on an algebra \(\mathcal A\) that is submultiplicative:</p>\[\|ab\|\leq\|a\|\,\|b\|\qquad(a,b\in\mathcal A).\]`,
    'algebra\\s+norms?',norms.outerHTML,{related:['unique-norm','minimal-norms','maximal-norms']});
  const minimal=paragraph('context-minimal-norms','Central to uniqueness-of-norm problems');
  glossary('minimal-norms','Minimal algebra norm','Definition · §1.1',minimal.id,
    tex`<p>An algebra norm \(p\) is <em>minimal</em> if every other algebra norm \(q\) dominates a positive multiple of \(p\):</p>\[\forall q\;\exists c>0\;\forall a\in\mathcal A,\qquad c\,p(a)\leq q(a).\]<p>The constant may depend on \(q\), but not on \(a\).</p>`,
    'minimality|minimal',minimal.outerHTML,{related:['algebra-norms','maximal-norms','bonsall']});
  glossary('maximal-norms','Maximal algebra norm','Definition · §1.1',minimal.id,
    tex`<p>An algebra norm \(p\) is <em>maximal</em> if it dominates every other algebra norm \(q\) up to a positive constant:</p>\[\forall q\;\exists C>0\;\forall a\in\mathcal A,\qquad q(a)\leq C\,p(a).\]<p>The constant may depend on \(q\), but not on \(a\).</p>`,
    'maximality|maximal',minimal.outerHTML,{related:['algebra-norms','minimal-norms','unique-norm']});
  const bonsall=paragraph('context-bonsall','Lastly, we turn our attention to another property');
  glossary('bonsall','Bonsall’s minimality property','Definition · §1.1',bonsall.id,
    tex`<p>An algebra norm \(p\) has <em>Bonsall’s minimality property</em> if every algebra norm \(q\) satisfying \(q(a)\leq p(a)\) for all \(a\) must equal \(p\).</p><p>This conclusion is exact equality of norms.</p>`,
    "Bonsall['’]s\\s+minimality\\s+property",bonsall.outerHTML,{related:['minimal-norms','algebra-norms']});
  const operator=paragraph('context-essential-norm','The term “operator');
  const equation=operator.nextElementSibling;
  if(!equation?.classList.contains('display-equation'))throw Error('Essential-norm equation missing from the paper.');
  glossary('dual-essential-norm','Dual essential norm','Theorem 1.5 · definition in §3','theorem-1-5',
    tex`<p>The <em>dual essential norm</em> of \(T:X\to Y\) is the essential norm of its adjoint \(T^*:Y^*\to X^*\):</p>\[\|T^*\|_e=\inf_{S\in\mathscr K(Y^*,X^*)}\|T^*-S\|.\]<p>The infimum runs over all compact operators from \(Y^*\) to \(X^*\).</p>`,
    'dual\\s+essential\\s+norms?|essential\\s+norms?\\s+of\\s+the\\s+adjoint(?:\\s+operator)?',resultPart('theorem-1-5')+operator.outerHTML+equation.outerHTML,
    {related:['essential-norm','theorem-1-5','theorem-1-7']});
  glossary('essential-norm','Essential norm','Definition · §3',operator.id,
    tex`<p>The <em>essential norm</em> of a bounded linear map \(T:X\to Y\) is its distance, in operator norm, to the compact operators:</p>\[\|T\|_e=\inf_{S\in\mathscr K(X,Y)}\|T-S\|.\]<p>Here \(\mathscr K(X,Y)\) denotes the compact operators from \(X\) to \(Y\).</p>`,
    '(?<!weak\\s)essential\\s+norms?',operator.outerHTML+equation.outerHTML,{related:['dual-essential-norm']});
  }else addPaperGlossary(article.paperId,{definition,glossary,add,resultPart,paper});
  addFormulaGlossary(article,{glossary,paper});
  // A numbered cross-reference uses the same source statement as the paper.
  for(const r of article.results)if(!entries.has(r.id))add(r.id,`${r.type} ${r.number}`,`${r.type} ${r.number} · §${r.number.split('.')[0]}`,r.id,r.statementHtml,null,{leanResult:r.id});
  for(const r of article.results)words.push({id:r.id,pattern:r.type+'\\s+'+r.number.replaceAll('.','\\.')});
  for(const equation of paper.querySelectorAll('.display-equation[id]')){
    const label=equation.querySelector('.equation-number')?.textContent;
    if(label)add(equation.id,'Equation '+label,'Equation '+label,equation.id,equation.outerHTML);
  }
  const bibliography=new Map(article.references.map(ref=>[ref.key,ref]));
  const bibliographyHTML=refs=>'<div class="reading-bibliography">'+refs.map(ref=>`<p><strong>[${ref.number}]</strong> ${ref.html}</p>`).join('')+'</div>';
  for(const ref of article.references)add('reference-'+ref.number,`Reference [${ref.number}]`,'Bibliography','reference-'+ref.number,bibliographyHTML([ref]),null,{bibliography:true});
  function citationEntry(keys){
    const refs=[...new Set(keys.split(',').map(key=>key.trim()))].map(key=>bibliography.get(key)).filter(Boolean);
    if(!refs.length)return null;
    if(refs.length===1)return 'reference-'+refs[0].number;
    const id='citation-'+refs.map(ref=>ref.number).join('-');
    if(!entries.has(id))add(id,`References [${refs.map(ref=>ref.number).join(', ')}]`,'Bibliography','reference-'+refs[0].number,bibliographyHTML(refs),null,{bibliography:true,related:refs.map(ref=>'reference-'+ref.number)});
    return id;
  }

  const preview=document.createElement('aside');preview.id='reading-preview';preview.hidden=true;
  preview.setAttribute('role','dialog');preview.setAttribute('aria-label','Reading reminder');
  preview.innerHTML='<div class="reading-preview-head"><span class="reading-source"></span><button data-dismiss-preview aria-label="Close reminder">×</button></div><h2></h2><div class="reading-preview-body reading-math"></div><div class="reading-preview-actions"><button data-pin-preview>Keep on the right ↗</button><button data-detail-preview>More detail</button><button data-jump-preview>Go to source</button></div>';
  document.body.append(preview);
  const note=document.createElement('section');note.id='reading-note';note.className='reading-note';note.hidden=true;note.setAttribute('aria-label','Reading note');
  note.innerHTML=`<header class="companion-head"><span class="reading-wordmark">Notes on the paper</span><button data-close-note aria-label="Close reading note">×</button></header>
    <div class="reading-note-nav"><button data-note-back hidden>‹ Previous reminder</button><button data-note-lean-back>Back to Lean</button></div>
    <div class="reading-note-scroll"><p class="reading-source"></p><h2 tabindex="-1"></h2>
      <div class="reading-level" role="group" aria-label="Reading depth"><button data-note-level="paper" aria-pressed="true">Paper wording</button><button data-note-level="detail" aria-pressed="false">More detail</button></div>
      <div class="reading-note-body reading-math"></div>
      <section class="reading-detail" hidden aria-label="Explanatory notes">
        <p class="detail-choice-label">What would help?</p><div class="detail-choices" role="group" aria-label="Choose an explanation"><button data-detail-topic="idea" aria-pressed="true">The idea</button><button data-detail-topic="notation" aria-pressed="false">The notation</button><button data-detail-topic="steps" aria-pressed="false">Step by step</button></div>
        <p class="detail-editorial">Explanatory note · added for this edition</p><div class="reading-explanation reading-math"></div><p class="detail-basis"></p>
      </section>
      <div class="reading-note-actions"><button data-note-jump>Go to source in the paper ↗</button><button data-note-lean>Lean formalisation →</button></div><div class="reading-related"></div>
      <details class="reading-question"><summary>Ask a further question</summary><p>For a question beyond these notes, copy the passage and your question into your chat.</p><label for="reading-question-input">What would you like explained?</label><textarea id="reading-question-input" rows="3" placeholder="For example: why is this bound uniform in n?"></textarea><button data-copy-question>Copy question with context</button><p class="question-status" role="status"></p><textarea class="question-export" aria-label="Question and paper context to copy" rows="8" readonly hidden></textarea></details>
    </div><footer class="reading-note-footer"><span>Kept beside your reading</span><button data-note-return hidden>Return to passage ↩</button></footer>`;
  side.append(note);
  let active=null,trail=[],origin=null,bookmark=null,previewEntry=null,previewTrigger=null,showTimer,hideTimer,previewVersion=0,lastPointerDown=-Infinity;
  let level='paper',topic='idea';const questions=new Map();
  const escapedPattern=words.map(w=>'('+w.pattern+')').join('|');
  const termPattern=new RegExp('(?<![\\p{L}\\p{N}_])(?:'+escapedPattern+')(?![\\p{L}\\p{N}_])','giu');
  function decorate(root,exclude){
    const walker=document.createTreeWalker(root,NodeFilter.SHOW_TEXT,{acceptNode(node){
      return node.parentElement.closest('a,button,summary,h1,h2,h3,pre,code,.math,.display-equation,mjx-container,.bibliography,.reading-bibliography,.reading-source,.reading-convention h3')?NodeFilter.FILTER_REJECT:NodeFilter.FILTER_ACCEPT;
    }});
    const nodes=[];while(walker.nextNode())nodes.push(walker.currentNode);
    for(const text of nodes){
      const matches=[...text.textContent.matchAll(termPattern)];if(!matches.length)continue;
      const fragment=document.createDocumentFragment();let offset=0;
      for(const match of matches){
        const index=match.slice(1).findIndex(x=>x!==undefined),id=words[index].id;
        fragment.append(text.textContent.slice(offset,match.index));
        if(id===exclude)fragment.append(match[0]);else{
          const button=document.createElement('span');button.setAttribute('role','button');button.tabIndex=0;button.className='reading-term';button.dataset.readingRef=id;button.textContent=match[0];
          button.setAttribute('aria-label',match[0]+' — show reminder');fragment.append(button);
        }
        offset=match.index+match[0].length;
      }
      fragment.append(text.textContent.slice(offset));text.replaceWith(fragment);
    }
    for(const math of root.querySelectorAll('.math,.equation-math')){
      if(math.closest('a,button,summary,h1,h2,h3'))continue;
      if(math.querySelector('mjx-container'))continue;
      const original=math.textContent;
      const section=Number(math.closest('.paper-section.level-1')?.id.replace('section-',''))||0;
      const annotated=annotateFormula(original,article.paperId,exclude,id=>entries.has(id),section);
      if(annotated!==original){math.textContent=annotated;continue;}
      const tex=math.textContent.replace(/^\\\(|\\\)$/g,'').trim();let id;
      if(article.paperId!=='jlms')id=paperNotation(article.paperId,tex);
      else if(/^\\proj\(/.test(tex))id='definition-4-6';
      else if(/^\\(?:finset|inset)\{/.test(tex))id='definition-4-4';
      else if(/^\\nonvan\{/.test(tex))id='definition-5-1';
      else if(/^S\(\\mathcal/.test(tex))id='definition-4-3';
      else if(/^\\(?:Tsupp|supp)\b/.test(tex))id='definition-4-9';
      else if(/^R_(?:\{|[A-Z])/.test(tex))id='definition-4-10';
      if(id&&id!==exclude&&entries.has(id)){math.dataset.readingRef=id;math.classList.add('reading-notation');math.tabIndex=0;math.setAttribute('role','button');math.setAttribute('aria-label',entries.get(id).title+' — show definition');}
    }
    for(const link of root.querySelectorAll('.cross-ref[data-target]'))if(entries.has(link.dataset.target)){
      link.dataset.readingRef=link.dataset.target;link.setAttribute('aria-label',entries.get(link.dataset.target).title+' — show statement');
    }
    for(const heading of root.querySelectorAll('.result-name[data-inspect]'))if(entries.has(heading.dataset.inspect))heading.dataset.readingRef=heading.dataset.inspect;
    for(const citation of root.querySelectorAll('.citation[data-cite]')){
      const id=citationEntry(citation.dataset.cite);if(id)citation.dataset.readingRef=id;
    }
    for(const trigger of root.querySelectorAll('[data-reading-ref]')){trigger.setAttribute('aria-haspopup','dialog');trigger.setAttribute('aria-controls','reading-preview');trigger.setAttribute('aria-expanded','false');}
  }
  function fill(element,html,exclude){
    window.MathJax?.typesetClear?.([element]);element.innerHTML=html;
    // Quoted passages must not duplicate anchors from the actual paper.
    for(const e of element.querySelectorAll('[id]'))e.removeAttribute('id');
    decorate(element,exclude);return typeset(element);
  }
  function positionPreview(){
    if(!previewTrigger?.isConnected||preview.hidden)return;
    const rect=previewTrigger.getBoundingClientRect();
    const belowSpace=innerHeight-rect.bottom-21,aboveSpace=rect.top-74;
    const below=belowSpace>=Math.min(460,innerHeight-82)||belowSpace>=aboveSpace;
    preview.style.maxHeight=Math.max(100,below?belowSpace:aboveSpace)+'px';
    const height=preview.offsetHeight;
    preview.style.left=Math.max(12,Math.min(rect.left,innerWidth-preview.offsetWidth-12))+'px';
    preview.style.top=(below?rect.bottom+9:Math.max(65,rect.top-height-9))+'px';
  }
  function hidePreview(){clearTimeout(showTimer);clearTimeout(hideTimer);previewVersion++;preview.hidden=true;previewTrigger?.setAttribute('aria-expanded','false');}
  function scheduleHide(){clearTimeout(showTimer);clearTimeout(hideTimer);hideTimer=setTimeout(()=>{if(!preview.matches(':hover')&&!preview.contains(document.activeElement))hidePreview();},180);}
  async function showPreview(trigger){
    const entry=entries.get(trigger.dataset.readingRef);if(!entry)return;
    clearTimeout(hideTimer);previewTrigger?.setAttribute('aria-expanded','false');previewTrigger=trigger;previewEntry=entry;
    const version=++previewVersion;preview.querySelector('.reading-source').textContent=entry.source;
    preview.querySelector('[data-detail-preview]').hidden=!detailNotes[entry.id];
    preview.querySelector('[data-jump-preview]').textContent=entry.bibliography?'Go to bibliography':'Go to source';
    preview.querySelector('h2').textContent=entry.title;preview.hidden=false;trigger.setAttribute('aria-expanded','true');
    const ready=fill(preview.querySelector('.reading-preview-body'),entry.html,entry.id);positionPreview();await ready;if(version===previewVersion)positionPreview();
  }
  function paperBookmark(trigger){
    const element=trigger?.closest('#paper p,#paper .paper-result,#paper .display-equation,#paper .paper-proof');
    return element?{element,offset:element.getBoundingClientRect().top}:null;
  }
  function visiblePaperBookmark(){
    const bounds=document.getElementById('paper-scroll').getBoundingClientRect();
    const element=[...paper.querySelectorAll('p,.display-equation,.result-heading')].find(e=>{const r=e.getBoundingClientRect();return r.height&&r.bottom>bounds.top+25&&r.top<bounds.bottom;});
    return element?{element,offset:element.getBoundingClientRect().top}:null;
  }
  function restoreBookmark(saved){if(saved?.element.isConnected){for(let p=saved.element.parentElement;p&&p!==paper;p=p.parentElement)if(p.tagName==='DETAILS')p.open=true;const scroller=document.getElementById('paper-scroll');scroller.scrollTo({top:scroller.scrollTop+saved.element.getBoundingClientRect().top-saved.offset,behavior:'instant'});}}
  function renderNote(){
    const entry=entries.get(active);note.querySelector('.reading-source').textContent=entry.source;
    note.querySelector('h2').textContent=entry.title;
    const original=entry.originalHtml?'<details class="reading-original"><summary>Original passage in the paper</summary><div>'+entry.originalHtml+'</div></details>':'';
    fill(note.querySelector('.reading-note-body'),entry.html+original,entry.id);
    note.querySelector('[data-note-level="paper"]').textContent=entry.wordingLabel||'Paper wording';
    note.querySelector('[data-note-back]').hidden=!trail.length;note.querySelector('[data-note-lean]').hidden=!entry.leanResult;
    note.querySelector('[data-note-return]').hidden=!bookmark;
    note.querySelector('[data-note-jump]').textContent=entry.bibliography?'Go to bibliography ↗':'Go to source in the paper ↗';
    note.querySelector('.reading-level').hidden=!!entry.bibliography;
    note.querySelector('.reading-question').hidden=!!entry.bibliography;
    note.querySelector('#reading-question-input').value=questions.get(active)||'';
    note.querySelector('.reading-question').open=false;note.querySelector('.question-status').textContent='';note.querySelector('.question-export').hidden=true;
    renderDepth();
    note.querySelector('.reading-note-scroll').scrollTop=0;
  }
  function renderDepth(){
    const entry=entries.get(active),details=detailNotes[active],expanded=level==='detail'&&!!details;
    note.querySelector('[data-note-level="detail"]').hidden=!details;
    for(const b of note.querySelectorAll('[data-note-level]'))b.setAttribute('aria-pressed',String(b.dataset.noteLevel===(expanded?'detail':'paper')));
    note.querySelector('.reading-note-body').hidden=expanded;note.querySelector('.reading-detail').hidden=!expanded;
    if(expanded){
      for(const b of note.querySelectorAll('[data-detail-topic]'))b.setAttribute('aria-pressed',String(b.dataset.detailTopic===topic));
      fill(note.querySelector('.reading-explanation'),detailHTML(active,topic,esc),active);
      note.querySelector('.detail-basis').textContent='Based on '+details.basis;
    }
    const related=[...new Set([...(entry.related||[]),...(expanded?details.uses||[]:[])])].filter(id=>entries.has(id)&&id!==active);
    note.querySelector('.reading-related').innerHTML=related.length?'<h3>Connections in the paper</h3>'+related.map(id=>`<button data-pin-reference="${esc(id)}">${esc(entries.get(id).title)} →</button>`).join(''):'';
  }
  function pin(id,trigger,{back=false,history=true,focus=false,detail=null}={}){
    if(!entries.has(id))return;
    const place=paperBookmark(trigger);
    const block=trigger?.closest('#paper .paper-result,#paper .paper-proof');
    if(block)selectPassage(block.dataset.result||block.dataset.proofOf);
    if(!active){origin=place;bookmark=null;trail=[];}else if(!back&&active!==id)trail.push({id:active,detail:level==='detail'?topic:null});
    if(place){origin=place;bookmark=null;}
    active=id;level=detail&&detailNotes[id]?'detail':'paper';topic=['idea','notation','steps'].includes(detail)?detail:'idea';hidePreview();openSide();side.querySelector('.lean-companion').hidden=true;note.hidden=false;
    renderNote();if(place)restoreBookmark(place);if(focus)note.querySelector('h2').focus({preventScroll:true});if(history)changed();
  }
  function hidePinned(){active=null;trail=[];note.hidden=true;side.querySelector('.lean-companion').hidden=false;hidePreview();}
  function goToSource(entry,trigger){
    if(active&&!bookmark)bookmark=origin||paperBookmark(trigger)||visiblePaperBookmark();
    hidePreview();jump(entry.target);note.querySelector('[data-note-return]').hidden=!bookmark;
  }
  document.addEventListener('pointerover',event=>{
    if(event.pointerType==='touch')return;
    if(preview.contains(event.target)){clearTimeout(hideTimer);return;}
    const trigger=event.target.closest('[data-reading-ref]');if(!trigger||trigger.contains(event.relatedTarget))return;
    clearTimeout(showTimer);clearTimeout(hideTimer);showTimer=setTimeout(()=>showPreview(trigger),320);
  });
  document.addEventListener('pointerout',event=>{
    const trigger=event.target.closest('[data-reading-ref]');
    if(trigger&&!trigger.contains(event.relatedTarget)&&!preview.contains(event.relatedTarget))scheduleHide();
    if(preview.contains(event.target)&&!preview.contains(event.relatedTarget)&&!previewTrigger?.contains(event.relatedTarget))scheduleHide();
  });
  document.addEventListener('focusin',event=>{const trigger=event.target.closest('[data-reading-ref]');if(trigger&&performance.now()-lastPointerDown>200){clearTimeout(showTimer);showPreview(trigger);}else if(preview.contains(event.target))clearTimeout(hideTimer);});
  document.addEventListener('focusout',event=>{if(!preview.contains(event.relatedTarget))scheduleHide();});
  document.addEventListener('pointerdown',event=>{lastPointerDown=performance.now();if(!preview.contains(event.target)&&!previewTrigger?.contains(event.target))hidePreview();});
  document.addEventListener('keydown',event=>{
    if(event.key==='Escape'&&!preview.hidden){event.preventDefault();if(preview.contains(document.activeElement))previewTrigger?.focus({preventScroll:true});hidePreview();}
    if(['Enter',' '].includes(event.key)&&event.target.matches('.reading-notation,.reading-term,.reading-formula-token')){event.preventDefault();pin(event.target.dataset.readingRef,event.target,{focus:true});}
  });
  document.addEventListener('click',async event=>{
    const term=event.target.closest('.reading-term,.reading-notation,.reading-formula-token');
    if(term){pin(term.dataset.readingRef,term,{focus:event.detail===0});return;}
    const button=event.target.closest('button');if(!button)return;
    if(button.hasAttribute('data-dismiss-preview')){hidePreview();return;}
    if(button.hasAttribute('data-pin-preview')){pin(previewEntry.id,previewTrigger,{focus:event.detail===0});return;}
    if(button.hasAttribute('data-detail-preview')){pin(previewEntry.id,previewTrigger,{detail:'idea',focus:event.detail===0});return;}
    if(button.dataset.explain){event.preventDefault();pin(button.dataset.explain,button,{detail:'idea',focus:event.detail===0});return;}
    if(button.dataset.noteLevel){level=button.dataset.noteLevel;renderDepth();changed(true);return;}
    if(button.dataset.detailTopic){topic=button.dataset.detailTopic;renderDepth();changed(true);return;}
    if(button.hasAttribute('data-expand-detail')){const steps=[...note.querySelectorAll('.detail-steps details')],expand=steps.some(d=>!d.open);for(const d of steps)d.open=expand;button.textContent=expand?'Fold every step':'Expand every step';return;}
    if(button.hasAttribute('data-jump-preview')){goToSource(previewEntry,previewTrigger);return;}
    if(button.dataset.pinReference){pin(button.dataset.pinReference,button);return;}
    if(button.hasAttribute('data-close-note')){const place=visiblePaperBookmark();hidePinned();closeSide();restoreBookmark(place);return;}
    if(button.hasAttribute('data-note-lean-back')){hidePinned();showLean();return;}
    if(button.hasAttribute('data-note-back')){const previous=trail.pop();if(previous)pin(previous.id,null,{back:true,detail:previous.detail});return;}
    if(button.hasAttribute('data-note-jump')){goToSource(entries.get(active),origin?.element);return;}
    if(button.hasAttribute('data-note-return')){restoreBookmark(bookmark);bookmark=null;button.hidden=true;return;}
    if(button.hasAttribute('data-note-lean')){const id=entries.get(active).leanResult;hidePinned();inspect(id);return;}
    if(button.hasAttribute('data-copy-question')){
      const input=note.querySelector('#reading-question-input'),status=note.querySelector('.question-status');
      if(!input.value.trim()){status.textContent='Write your question first.';input.focus();return;}
      const entry=entries.get(active),passage=document.createElement('div');passage.innerHTML=entry.html;
      const text=`${article.paperLabel} paper — ${entry.title}\n${entry.source}\n\nPaper passage (mathematics in TeX):\n${passage.textContent.trim()}\n\nMy question:\n${input.value.trim()}\n\nReading location: ${location.href}\nPaper edition SHA-256: ${article.sourceHash}\nPlease distinguish your explanation from the paper and from any Lean verification.`;
      try{await navigator.clipboard.writeText(text);status.textContent='Copied. Paste it into your chat to ask.';}catch{const output=note.querySelector('.question-export');output.value=text;output.hidden=false;output.focus();output.select();status.textContent='Select and copy the prepared question below.';}
    }
  });
  note.querySelector('#reading-question-input').addEventListener('input',event=>questions.set(active,event.target.value));
  note.addEventListener('toggle',()=>{const steps=[...note.querySelectorAll('.detail-steps details')],button=note.querySelector('[data-expand-detail]');if(button)button.textContent=steps.every(d=>d.open)?'Fold every step':'Expand every step';},true);
  document.getElementById('paper-scroll').addEventListener('scroll',hidePreview,{passive:true});
  note.querySelector('.reading-note-scroll').addEventListener('scroll',hidePreview,{passive:true});
  window.addEventListener('resize',hidePreview);
  decorate(paper);
  for(const block of paper.querySelectorAll('.paper-result,.paper-proof')){
    const id=block.dataset.result||block.dataset.proofOf;if(!detailNotes[id])continue;
    const button=document.createElement('button');button.className='more-detail';button.dataset.explain=id;button.textContent='More detail';button.setAttribute('aria-label','More detail about '+entries.get(id).title);
    (block.querySelector(':scope > .result-body > .result-footer')||block.querySelector(':scope > summary')).append(button);
  }
  return {get activeId(){return active;},get detailTopic(){return level==='detail'?topic:null;},pin,hidePinned,hidePreview,entries,capturePassage:visiblePaperBookmark,restorePassage:restoreBookmark,
    activateFormulaReferences:root=>activateFormulaReferences(root,entries)};
}
