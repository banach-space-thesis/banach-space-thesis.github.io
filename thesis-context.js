// Website navigation follows the existing thesis structure. No thesis text is published here.
export const thesisParts = [
  {number:'I', title:'Uniqueness of algebra norms', papers:[
    {id:'jlms', chapter:'Chapter 2', title:'Algebra norms and Calkin algebras'},
    {id:'pems', chapter:'Chapter 3', title:'Weak Calkin algebra norms and weak compactness'},
  ]},
  {number:'II', title:'Primariness and factorisation properties', papers:[
    {id:'pfp', chapter:'Part II introduction', title:'Primariness and the factorisation properties'},
    {id:'upfp', chapter:'Chapter 4', title:'Permanence of the UPFP under sequence-space sums'},
    {id:'lpck', chapter:'Chapter 5', title:'Primariness of ℓₚ(C(K))-spaces'},
  ]},
  {number:'III', title:'Exotic spaces of continuous functions', papers:[
    {id:'sigma', chapter:'Chapter 6', title:'Nonprimariness of Banach lattices'},
    {id:'posets', chapter:'Chapter 7', title:'Few operators relative to partially ordered sets'},
    {id:'jfa', chapter:'Chapter 8', title:'Few operators and injective tensor products'},
  ]},
];

export function createThesisContext({paperId, getMode}) {
  const dialog=document.getElementById('thesis-library');
  const opener=document.getElementById('thesis-library-button');
  const context=document.getElementById('thesis-context');
  const part=thesisParts.find(p=>p.papers.some(paper=>paper.id===paperId));
  const place=part?.papers.find(paper=>paper.id===paperId);
  const picker=document.getElementById('paper-select');
  let trigger=opener;

  if(part&&place){
    context.textContent=place.id==='pfp'?'Part II · Introduction':`Part ${part.number} · ${place.chapter}`;
    context.setAttribute('aria-label',context.textContent+' — show thesis and papers');
    context.title=part.title+' · '+place.title;
  }else context.hidden=true;

  function chooseCollection(name){
    document.getElementById('thesis-collections').hidden=name!=='collections';
    document.getElementById('thesis-full-preview').hidden=name!=='thesis';
    document.getElementById('thesis-later-preview').hidden=name!=='later';
    document.getElementById('thesis-library-back').hidden=name==='collections';
    dialog.scrollTop=0;
  }
  function close(returnFocus=false){
    if(!dialog.open)return;
    dialog.close();
    if(returnFocus)trigger.focus({preventScroll:true});
  }
  function open(button){
    if(dialog.open){close(true);return;}
    trigger=button;
    chooseCollection('collections');
    const left=opener.getBoundingClientRect().left;
    dialog.style.left=Math.max(10,Math.min(left,innerWidth-390))+'px';
    dialog.show();
    for(const button of [opener,context])button.setAttribute('aria-expanded','true');
  }
  opener.onclick=()=>open(opener);context.onclick=()=>open(context);
  dialog.addEventListener('close',()=>{
    for(const button of [opener,context])button.setAttribute('aria-expanded','false');
  });
  dialog.querySelector('[data-close-thesis-library]').onclick=()=>close(true);
  dialog.querySelector('[data-choose-papers]').onclick=()=>{
    close();picker.focus({preventScroll:true});
    // Keep the existing native, grouped paper selector as the only paper list.
    if(typeof picker.showPicker==='function'){
      try{picker.showPicker();}catch{/* Focusing the selector remains useful on older browsers. */}
    }
  };
  dialog.addEventListener('click',event=>{
    const choice=event.target.closest('[data-thesis-view]');
    if(!choice)return;
    chooseCollection(choice.dataset.thesisView);
    const target=choice.dataset.thesisView==='collections'?dialog.querySelector('[data-thesis-view="thesis"]'):dialog.querySelector('[data-thesis-view="collections"]');
    target.focus({preventScroll:true});
  });
  document.addEventListener('pointerdown',event=>{
    if(dialog.open&&!dialog.contains(event.target)&&!opener.contains(event.target)&&!context.contains(event.target))close();
  });
  document.addEventListener('keydown',event=>{
    if(dialog.open&&event.key==='Escape'){event.preventDefault();close(true);}
  });
}
