// Match the notation introduced by this paper, including terms inside larger
// formulae. Bare letters are deliberately left alone: their meaning varies.
function space(s,i){while(/\s/.test(s[i]||'')&&i<s.length)i++;return i;}
function group(s,i,open,close){
  if(s[i]!==open)return null;
  let depth=0;
  for(let j=i;j<s.length;j++){
    if(s[j]==='\\'&&/[{}()]/.test(s[j+1]||'')){j++;continue;}
    if(s[j]===open)depth++;
    if(s[j]===close&&!--depth)return j+1;
  }
  return null;
}
function atom(s,i){
  i=space(s,i);if(i>=s.length)return null;
  if(s[i]==='{')return group(s,i,'{','}');
  if(s[i]==='\\'){
    const command=/^\\[A-Za-z]+/.exec(s.slice(i));
    if(!command)return i+2;
    let end=i+command[0].length;
    const next=space(s,end);
    if(s[next]==='{')end=group(s,next,'{','}')||end;
    return end;
  }
  return i+1;
}
function scripts(s,i){
  for(;;){const j=space(s,i);if(!['_','^'].includes(s[j]))return i;const end=atom(s,j+1);if(!end)return i;i=end;}
}
function parentheses(s,i){
  i=space(s,i);
  const left=/^\\(?:left|bigl?|Bigl?|biggl?|Biggl?)\s*/.exec(s.slice(i));
  if(left)i+=left[0].length;
  return group(s,i,'(',')');
}
function jlmsTermAt(s,i){
  if(s[i]==='S'&&!/[A-Za-z\\]/.test(s[i-1]||'')){
    const start=space(s,i+1),end=parentheses(s,start);
    if(end&&/^\s*(?:\\(?:left|bigl?|Bigl?|biggl?|Biggl?)\s*)?\(\s*\\mathcal\b/.test(s.slice(start,end)))
      return {end,id:'definition-4-3'};
  }
  if(s[i]==='R'&&s[i+1]==='_'&&!/[A-Za-z\\]/.test(s[i-1]||'')){
    const end=atom(s,i+2);if(end)return {end,id:'definition-4-10'};
  }
  if(s[i]!=='\\')return null;
  const command=/^\\([A-Za-z]+)/.exec(s.slice(i));if(!command)return null;
  const name=command[1],after=space(s,i+command[0].length);
  const braceRefs={finset:'definition-4-4',inset:'definition-4-4',nonvan:'definition-5-1',Tsupp:'definition-4-9'};
  if(braceRefs[name]&&s[after]==='{'){
    const end=group(s,after,'{','}');if(end)return {end,id:braceRefs[name]};
  }
  if(name==='proj'){
    const end=parentheses(s,after);if(end)return {end,id:'definition-4-6'};
  }
  if(name==='supp'){
    const end=parentheses(s,after)||atom(s,after);if(end)return {end:scripts(s,end),id:'definition-4-9'};
  }
  return null;
}

// Each rule belongs to one article. Parentheses and scripts are read as TeX
// groups, so a reminder covers the term, even when it occurs in a longer sum.
function call(s,i,prefix,id,accept=()=>true){
  const match=prefix.exec(s.slice(i));if(!match)return null;
  const end=parentheses(s,i+match[0].length);
  return end&&accept(s.slice(i,end))?{end,id}:null;
}
function token(s,i,prefix,id){
  const match=prefix.exec(s.slice(i));if(!match)return null;
  let depth=0;for(const c of match[0]){if(c==='{')depth++;if(c==='}')depth--;}
  return depth===0?{end:i+match[0].length,id}:null;
}
function indexed(s,i,prefix,id,accept=()=>true,bothScripts=false){
  const match=prefix.exec(s.slice(i));if(!match)return null;
  const after=i+match[0].length,j=space(s,after);
  const end=bothScripts?scripts(s,after):(s[j]==='_'?atom(s,j+1):after);
  return end>i+match[0].length&&accept(s.slice(i,end))?{end,id}:null;
}
function weakNorm(s,i){
  const start=/^(?:\\left\s*)?\\lVert(?![A-Za-z])|^(?:\\left\s*)?\\\|/.exec(s.slice(i));if(!start)return null;
  // Avoid opening a reminder between a sizing command and its delimiter.
  if(s.slice(0,i).endsWith('\\left'))return null;
  const after=i+start[0].length;
  const closing=/(?:\\right\s*)?\\rVert(?![A-Za-z])|(?:\\right\s*)?\\\|/.exec(s.slice(after));if(!closing)return null;
  if(/\\lVert|\\\|/.test(s.slice(after,after+closing.index)))return null;
  const end=after+closing.index+closing[0].length;
  const sub=/^\s*_\s*(?:w\b|\{w\})/.exec(s.slice(end));
  return sub?{end:end+sub[0].length,id:'weak-essential-norm'}:null;
}
function paperTermAt(s,i,paper,section){
  if(paper==='jlms')return jlmsTermAt(s,i);
  if(s[i-1]==='\\')return null;
  let term;
  if(paper==='pems')return weakNorm(s,i)
    ||call(s,i,/^m\b/,'minimum-modulus')
    ||call(s,i,/^\\Delta\b/,'equi-integrability')
    ||call(s,i,/^\\varepsilon\b/,'definition-6-1',x=>/\(\s*(?:A|\\mathcal)/.test(x))
    ||call(s,i,/^\\alpha_\{\\Theta\}/,'local-weak-modulus')
    ||token(s,i,/^\\Sigma_\{?\\mu\}?/,'definition-3-4')
    ||(section>=3&&section<=4?indexed(s,i,/^k(?=\s*[_^])/,'truncated-kernel',x=>/^k_(?:[ns]|\{[ns]\})/.test(x)):null);
  if(paper==='sigma')return call(s,i,/^\\operatorname\{JL\}/,'jl-space')
    ||call(s,i,/^\\operatorname\*?\{ult\}/,'stone-space')
    ||call(s,i,/^\\operatorname\{fin\}/,'finite-subsets')
    ||call(s,i,/^M_\{?1\}?/,'measure-ball')
    ||call(s,i,/^M\b/,'measure-space',x=>/\\(?:mathfrak|mathcal|tilde)/.test(x))
    ||token(s,i,/^\\(?:mathrm|text)\{DP\}/,'definition-3-3')
    ||token(s,i,/^K_\{\\mathcal\{[AB]\}\}/,'stone-space');
  if(['pfp','upfp','lpck'].includes(paper)){
    const factor=paper==='pfp'?'definition-2-4':'definition-2-2';
    term=token(s,i,/^\\(?:mathrm|text)\{(?:UPFP|PFP)\}/,factor)
      ||token(s,i,/^(?:UPFP|PFP)\b/,factor);
    if(term)return term;
  }
  if(paper==='pfp')return call(s,i,/^d_\{BM\}/,'definition-2-1')
    ||indexed(s,i,/^\\simeq(?![A-Za-z])/,'controlled-isomorphism')
    ||call(s,i,/^X_\{\\mathcal\{F\}\}/,'filter-space')
    ||token(s,i,/^X_\{\\mathcal\{F\}\}|^c_\{\\mathcal\{F\}\}/,'filter-space')
    ||(section===6?indexed(s,i,/^\\mathcal\{F\}/,'trace-filter'):null)
    ||(section===6?indexed(s,i,/^P(?=\s*[_^])/,'filter-projection'):null)
    ||(section===6?token(s,i,/^M_\{?a\}?/,'filter-multiplier'):null);
  if(['upfp','lpck'].includes(paper)){
    term=call(s,i,/^E\b/,'sequence-sum')
      ||call(s,i,/^\\ell_(?:\{[^{}]+\}|[p12])/,'classical-sum')
      ||call(s,i,/^c_\{?0\}?/,'classical-sum')
      ||indexed(s,i,/^P(?=\s*[_^])/,'coordinate-projection',x=>!x.includes(','))
      ||indexed(s,i,/^J(?=\s*[_^])/,'coordinate-inclusion',x=>!x.includes(','))
      ||indexed(s,i,/^T(?=\s*[_^])/,'operator-matrix',x=>x.includes(','))
      ||call(s,i,/^\\operatorname\{supp\}/,'sequence-support');
    if(term)return term;
    if(paper==='upfp')return call(s,i,/^\\operatorname\{diag\}/,'definition-2-3');
    return call(s,i,/^C\b/,'ordinal-functions',x=>/\\(?:alpha|omega|eta|beta)/.test(x))
      ||call(s,i,/^\\tau\b/,'ordinal-type')
      ||token(s,i,/^[RS]_\{?A\}?/,'definition-2-8');
  }
  if(['posets','jfa'].includes(paper)){
    term=indexed(s,i,/^K(?=\s*[_^])/,'mrowka-space',x=>/^K_\{\\mathcal\{[AB]\}/.test(x))
      ||call(s,i,/^U\b/,'mrowka-neighbourhood',x=>/^U\s*(?:\\left)?\(\s*A(?:\b|_)/.test(x))
      ||call(s,i,/^s\b/,'mrowka-support',x=>/\(\s*(?:[fg](?:\b|_)|\\mathcal\{[XY]\})/.test(x))
      ||call(s,i,/^\\mathscr\{X\}/,'separable-operators')
      ||call(s,i,/^\\mathscr\{K\}/,'compact-operators')
      ||call(s,i,/^\\mathscr\{B\}/,'bounded-operators');
    if(term)return term;
    if(paper==='posets')return call(s,i,/^\\operatorname\{\\mathbf\{IA\}\}/,'incidence-algebra',x=>!x.includes('c_{0}')&&!x.includes('c_0'))
      ||call(s,i,/^\\operatorname\{\\mathbf\{IA\}\}/,'c0-incidence-algebra')
      ||indexed(s,i,/^\\iota(?![A-Za-z])/,'order-inclusion',x=>x.includes(','))
      ||token(s,i,/^M(?:\^\{?r\}?_\{?T\}?|_\{?T\}?\^\{?r\}?)/,'definition-4-16')
      ||(section>=4?indexed(s,i,/^M(?=\s*[_^])/,'matrix-restriction',x=>x.includes('_')&&x.includes('^'),true):null)
      ||(section>=4?token(s,i,/^\\mathbb\{M\}(?![_^])/,'bounded-matrices'):null)
      ||token(s,i,/^\\mathcal\{P\}\^\{?\*\}?/,'definition-6-13');
    return token(s,i,/^\\(?:hat|widehat)\{?\\otimes\}?_\{?\\varepsilon\}?/,'injective-tensor')
      ||token(s,i,/^\\(?:hat|widehat)\{?\\otimes\}?_\{?\\alpha\}?/,'uniform-tensor')
      ||call(s,i,/^\\varepsilon\b/,'injective-tensor')
      ||call(s,i,/^\\alpha\b/,'tensor-norm')
      ||token(s,i,/^\\pi_\{?k\}?/,'evaluation-map')
      ||token(s,i,/^\\iota_\{?e\}?/,'tensor-inclusion')
      ||token(s,i,/^(?:T|S|\\lambda)_\{e,k\}/,'coordinate-operator')
      ||token(s,i,/^Y_\{E_\{?0\}?\}/,'definition-3-3');
  }
  return null;
}

export function annotateFormula(s,paper,exclude,hasReference=()=>true,section=0){
  function annotate(s,skipFirst=false){
    let rendered='';
    for(let i=0;i<s.length;){
      const term=!(skipFirst&&i===0)&&paperTermAt(s,i,paper,section);
      if(term){
        const original=s.slice(i,term.end),nested=annotate(original,true);
        rendered+=term.id!==exclude&&hasReference(term.id)?`\\readerterm{${term.id}}{${nested}}`:nested;
        i=term.end;
      }else{
        // Do not interpret text inside a TeX command name as mathematical notation.
        const command=s[i]==='\\'&&/^\\[A-Za-z]+/.exec(s.slice(i));
        let end=command?i+command[0].length:i+1;
        if(command&&/^\\(?:text|textrm|textit|textbf)$/.test(command[0]))end=atom(s,end)||end;
        rendered+=s.slice(i,end);i=end;
      }
    }
    return rendered;
  }
  return annotate(s);
}

// Short reminders are restatements of the cited passage. Keep that passage
// available in the same card, rather than substituting a nearby definition.
export function addFormulaGlossary(article,{glossary,paper}){
  const t=String.raw,results=new Map(article.results.map(r=>[r.id,r]));
  function note(id,title,target,html,related=[]){
    const result=results.get(target),passage=paper.querySelector('[id="'+target+'"]');
    if(!result&&!passage)throw Error('Missing notation passage: '+article.paperId+' / '+target);
    glossary(id,title,result?`${result.type} ${result.number}`:'Notation in the paper',target,html,null,
      result?.statementHtml||passage.outerHTML,{related});
  }
  const id=article.paperId;
  if(id==='pems'){
    note('equi-integrability','Modulus of equi-integrability','definition-3-16',t`<p>\(\Delta(A)\) measures how much mass the functions in a bounded set \(A\subseteq L_1\) can concentrate on sets of arbitrarily small measure.</p>\[\Delta(A)=\limsup_{\mu(B)\to0}\sup_{f\in A}\|\chi_Bf\|.\]<p>For an operator \(T:E\to L_1\), the convention is \(\Delta(T)=\Delta(T[B_E])\).</p>`,['definition-3-16','operator-equi-integrability']);
    note('operator-equi-integrability','Equi-integrability of an operator','S3.SS4.p2',t`<p>\(\Delta(T)\) means \(\Delta(T[B_E])\): apply the modulus of equi-integrability to the image of the unit ball. It vanishes precisely when \(T\) is weakly compact.</p>`,['equi-integrability']);
    note('local-weak-modulus','The localized modulus αΘ','S4.SS4.p8',t`<p>Fix a measurable set \(\Theta\subseteq Y\) of finite measure. This quantity keeps the part of \(T\) outside \(\Theta\) and measures concentration on small subsets of \(\Theta\):</p>\[\alpha_\Theta(T)=\limsup_{\nu(B)\to0,\,B\subseteq\Theta}\|\chi_{Y\setminus\Theta}T+\chi_BT\|.\]`,['equi-integrability','weak-essential-norm']);
    note('truncated-kernel','Truncated kernel','definition-3-13',t`<p>\(k_s\) keeps the part of the integral kernel where its magnitude is at least \(s\):</p>\[k_s(x,y)=k(x,y)\,\mathbf1_{\{|k(x,y)|\ge s\}}.\]<p>\(K_s\) is the integral operator with this kernel; \(k_n\) denotes an integer threshold.</p>`);
  }
  if(id==='sigma'){
    note('finite-subsets','Finite subsets','S3.SS1.p1',t`<p>\(\operatorname{fin}(\omega)\) is the family of all finite subsets of the nonnegative integers. The same notation is used for the other countable sets in the construction.</p>`);
    note('jl-space','Johnson–Lindenstrauss space','S3.SS1.p2',t`<p>For an almost disjoint family \(\mathcal B\), \(\operatorname{JL}(\mathcal B)\) is the closed linear span in \(\ell_\infty\) of the singleton indicators, the indicators of members of \(\mathcal B\), and the constant function \(1\).</p><p>With two families, \(\operatorname{JL}(\mathcal B,\widetilde{\mathcal B})\) denotes the direct sum of their two spaces.</p>`,['almost-disjoint','jl-direct-sum','stone-space']);
    note('jl-direct-sum','The two Johnson–Lindenstrauss spaces','S3.SS4.p4',t`\[\operatorname{JL}(\mathcal B,\widetilde{\mathcal B})=\operatorname{JL}(\mathcal B)\oplus\operatorname{JL}(\widetilde{\mathcal B}).\]<p>The corresponding measure space is their dual.</p>`,['jl-space','measure-space']);
    note('stone-space','Stone space and its compact model','S3.SS1.p2',t`<p>\(\operatorname{ult}(\mathfrak B)\) is the Stone space of the Boolean algebra \(\mathfrak B\): its points are ultrafilters, with clopen sets corresponding to members of the algebra.</p><p>For \(\mathfrak B=[\mathcal B\cup\operatorname{fin}(\omega)]\), the paper writes this compact space as \(K_{\mathcal B}\): the integers, one limit point for each member of \(\mathcal B\), and the point at infinity.</p>`,['jl-space']);
    note('measure-space','The dual measure space','S3.SS1.p3',t`<p>\(M(\mathfrak B)\) consists of real finitely additive measures on the Boolean algebra \(\mathfrak B\), with finite total variation. It is the dual of the corresponding Johnson–Lindenstrauss space.</p><p>\(M(\mathfrak B,\widetilde{\mathfrak B})\) denotes \(M(\mathfrak B)\oplus M(\widetilde{\mathfrak B})\).</p>`,['jl-space','jl-direct-sum','measure-ball']);
    note('measure-ball','Unit ball of the measure space','S3.SS4.p5',t`<p>The subscript \(1\) denotes measures of total variation at most one. \(M_1(\mathfrak B,\widetilde{\mathfrak B})\) carries the weak* topology of the dual of \(\operatorname{JL}(\mathcal B,\widetilde{\mathcal B})\).</p><p>Section 4 uses the same convention for the power-set algebras on the two countable sets.</p>`,['measure-space','definition-4-1']);
  }
  if(id==='pfp'){
    note('controlled-isomorphism','Isomorphism with a distortion bound','definition-2-1',t`<p>\(E\simeq_C F\) means that some bounded isomorphism \(T:E\to F\) satisfies \(\|T\|\,\|T^{-1}\|\le C\).</p><p>This requires an actual isomorphism with that bound. A bound on the Banach–Mazur infimum alone allows an arbitrarily small positive error.</p>`,['definition-2-1']);
    note('filter-space','The space associated to a filter','S6.p2',t`<p>\(X_{\mathcal F}=c_{\mathcal F}(\Gamma)\) consists of bounded scalar functions that tend to zero along the filter \(\mathcal F\):</p>\[\{\gamma:|x(\gamma)|<\varepsilon\}\in\mathcal F\quad(\varepsilon>0).\]<p>\(X_{\mathcal F}(A)\) is the subspace supported on \(A\).</p>`,['filter-projection','trace-filter']);
    note('filter-projection','Coordinate projection','S6.p2',t`<p>\(P_A\) keeps the coordinates in \(A\) and sets the others to zero. Thus \(X_{\mathcal F}(A)=P_AX_{\mathcal F}\).</p>`,['filter-space']);
    note('filter-multiplier','Multiplication operator','S6.p2',t`<p>For a bounded scalar function \(a\), \(M_a\) multiplies each coordinate by the corresponding value of \(a\):</p>\[(M_ax)(\gamma)=a(\gamma)x(\gamma).\]`,['filter-space']);
    note('trace-filter','Trace of a filter','S6.p3',t`<p>The trace of \(\mathcal F\) on \(A\) is</p>\[\mathcal F_A=\{B\subseteq A:B\cup(\Gamma\setminus A)\in\mathcal F\}.\]<p>Restriction to \(A\) identifies \(X_{\mathcal F}(A)\) with the corresponding trace-filter space. For an improper trace, the paper uses \(\ell_\infty(A)\).</p>`,['filter-space']);
  }
  if(['upfp','lpck'].includes(id)){
    const sum=id==='upfp'?'S2.SS1.p1':'S2.SS1.SSS1.p1';
    const coordinates=id==='upfp'?'S2.SS1.p2':'S2.SS1.SSS1.p2';
    const matrix=id==='upfp'?'S2.SS1.p3':'S2.SS1.SSS1.p3';
    note('sequence-sum','The E-sum of Banach spaces',sum,t`<p>The notation \(E(X)\), or \(E(M,X)\), uses the chosen unconditional basis of \(E\) to measure the sequence of coordinate norms.</p>\[\|(x_n)\|=\left\|\sum_n\|x_n\|e_n\right\|_E.\]<p>For these basis sums, the series converges in \(E\). The \(\ell_\infty\) case uses bounded sequences with the supremum norm. A set of indices restricts the allowed coordinates.</p>`,['coordinate-projection','coordinate-inclusion','classical-sum']);
    note('classical-sum','Classical vector-valued sequence spaces',sum,t`<p>For \(1\le p<\infty\), \(\ell_p(X)\) consists of sequences in \(X\) with norm \((\sum_n\|x_n\|^p)^{1/p}\). For \(p=\infty\), the norm is \(\sup_n\|x_n\|\).</p><p>\(c_0(X)\) consists of sequences whose norms tend to zero, with the supremum norm. A set of indices restricts the allowed coordinates.</p>`,['sequence-sum','bounded-sum']);
    note('coordinate-projection','Coordinate projection',coordinates,t`<p>\(P_M\) keeps the coordinates indexed by \(M\). For a singleton, \(P_n(x)=x_n\), under the natural identification with \(X\).</p>`,['coordinate-inclusion','operator-matrix']);
    note('coordinate-inclusion','Coordinate inclusion',coordinates,t`<p>\(J_M\) includes the sequences supported on \(M\) in the full sequence space. For a singleton, \(J_nx\) places \(x\) in coordinate \(n\) and zero elsewhere.</p>\[P_MJ_M=I_{E(M,X)}.\]`,['coordinate-projection','operator-matrix']);
    note('sequence-support','Support of a sequence',coordinates,t`\[\operatorname{supp}(x)=\{n:x_n\ne0\}.\]<p>These are precisely the coordinates where the sequence is nonzero.</p>`);
    note('operator-matrix','An entry of the operator matrix',matrix,t`\[T_{n,m}=P_nTJ_m.\]<p>This map places a vector in coordinate \(m\), applies \(T\), and reads coordinate \(n\). It is an operator between the coefficient spaces.</p>`,['coordinate-projection','coordinate-inclusion']);
    if(id==='lpck'){
      note('bounded-sum','The ℓ∞-sum','S2.SS1.SSS2.p1',t`<p>\(\ell_\infty(X)\) is the space of bounded sequences in \(X\), with norm \(\sup_n\|x_n\|\). Finitely supported sequences need not be dense here.</p>`);
      note('ordinal-functions','Continuous functions on an ordinal interval','S1.p2',t`<p>\(C(\alpha)\) denotes the continuous scalar-valued functions on the compact ordinal interval \([0,\alpha]\), with its order topology and the supremum norm.</p>\[\|f\|=\sup_{\xi\le\alpha}|f(\xi)|.\]`);
      note('ordinal-type','Type of a compact ordinal set','S2.SS2.p2',t`<p>\(\tau(A)\) is the first ordinal stage at which the successive Cantor–Bendixson derivatives of \(A\) form a finite set. Together with the cardinality of that finite derivative, it gives the characteristic system.</p>`);
    }
  }
  if(['posets','jfa'].includes(id)){
    const support=id==='posets'?'definition-4-2':'definition-4-3';
    note('mrowka-space','Mrówka space','definition-4-1',t`<p>\(K_{\mathcal A}\) is built from an almost disjoint family \(\mathcal A\). It has isolated points \(x_n\) and a point \(y_A\) for each \(A\in\mathcal A\). Neighbourhoods of \(y_A\) contain all but finitely many \(x_n\) with \(n\in A\).</p>`,['mrowka-neighbourhood']);
    note('mrowka-neighbourhood','A basic neighbourhood in a Mrówka space','definition-4-1',t`\[U(A,F)=\{y_A\}\cup\{x_n:n\in A\setminus F\}.\]<p>Here \(F\) is finite. The abbreviation \(U(A)\) means \(U(A,\varnothing)\).</p>`,['mrowka-space']);
    note('mrowka-support','Support on the almost disjoint family',support,id==='posets'
      ?t`<p>\(s(f)\) records the members of \(\mathcal A\) at whose associated nonisolated points \(f\) is nonzero:</p>\[s(f)=\{A\in\mathcal A:f(y_A)\ne0\}.\]<p>For a family of functions, \(s(\mathcal X)=\bigcup_{f\in\mathcal X}s(f)\).</p>`
      :t`<p>\(s(f)\) records the members of \(\mathcal A\) where \(f\) is nonzero at some point of the corresponding fibre:</p>\[s(f)=\{A\in\mathcal A:\exists k\in M,\ f(k,y_A)\ne0\}.\]<p>For a family of functions, \(s(\mathcal X)=\bigcup_{f\in\mathcal X}s(f)\).</p>`,['mrowka-space']);
    const ideals=id==='jfa'?'S1.p13':'S1.p14';
    note('separable-operators','Operators with separable range',ideals,t`<p>\(\mathscr X(Y)\) denotes the ideal of bounded operators on \(Y\) whose ranges are separable.</p>`);
    note('compact-operators','Compact operators',id==='jfa'?'S1.p13':'proposition-1-3',t`<p>\(\mathscr K(Y)\) denotes the ideal of compact operators on \(Y\): the image of the unit ball has compact closure.</p>`);
    note('bounded-operators','Bounded linear operators',id==='jfa'?'S1.p13':'proposition-1-3',t`<p>\(\mathscr B(Y,Z)\) is the Banach space of bounded linear maps from \(Y\) to \(Z\), with the operator norm. \(\mathscr B(Y)\) means \(\mathscr B(Y,Y)\).</p>`);
    if(id==='posets'){
      note('order-inclusion','Inclusion associated to the order','definition-6-1',t`<p>For \(s\le t\), \(\iota_{s,t}:X_s\to X_t\) is the distinguished isometric inclusion. The inclusions agree with composition:</p>\[\iota_{s,t}\iota_{r,s}=\iota_{r,t}\quad(r\le s\le t).\]<p>They describe the scalar part of an operator along the order.</p>`);
      note('bounded-matrices','Matrices with bounded row sums','definition-4-11',t`<p>\(\mathbb M\) consists of scalar matrices with uniformly bounded absolute row sums:</p>\[\|M\|=\sup_k\sum_n|m_{k,n}|<\infty.\]<p>Such a matrix acts on \(\ell_\infty\) by \((Mf)(k)=\sum_nm_{k,n}f(n)\).</p>`);
      note('matrix-restriction','Restriction of a matrix to rows and columns','definition-4-13',t`<p>\(M_B^A\) keeps the rows in \(B\) and the columns in \(A\), replacing every other entry by zero.</p>`);
      note('incidence-algebra','Incidence algebra','definition-6-4',t`<p>\(\operatorname{\mathbf{IA}}(\mathcal P)\) consists of scalar functions on pairs \((s,t)\) that vanish unless \(s\le t\). Multiplication is convolution along the order:</p>\[(f\star g)(s,t)=\sum_{s\le r\le t}f(s,r)g(r,t).\]`);
      note('c0-incidence-algebra','The c₀-incidence algebra','definition-6-9',t`<p>\(\operatorname{\mathbf{IA}}(\mathcal P,c_0)\) consists of bounded operators on \(c_0(\mathcal P)\) whose matrix entries vanish unless \(s\le t\):</p>\[e_s^*Te_t=0\quad(s\not\le t).\]`,['incidence-algebra']);
    }else{
      note('injective-tensor','Injective tensor norm and completion','S2.SS1.p3',t`<p>The injective norm tests a tensor against norm-one functionals on both factors:</p>\[\varepsilon\left(\sum_i x_i\otimes y_i\right)=\sup_{\varphi\in B_{X^*},\,\psi\in B_{Y^*}}\left|\sum_i\varphi(x_i)\psi(y_i)\right|.\]<p>\(X\hat\otimes_\varepsilon Y\) is the completion in this norm.</p>`,['definition-2-3']);
      note('uniform-tensor','Tensor completion in the norm α','S2.SS1.p3',t`<p>\(E\hat\otimes_\alpha X\) is the completion of the algebraic tensor product in the norm \(\alpha\).</p><p>In the main theorem, \(\alpha\) is a uniform crossnorm. Uniformity ensures \(\|U\otimes R\|\le\|U\|\,\|R\|\) for bounded maps between the two pairs of factors.</p>`,['definition-2-3','definition-2-4','injective-tensor']);
      note('tensor-norm','The tensor norm α','S2.SS1.p3',t`<p>\(\alpha(u)\) is the chosen norm of the algebraic tensor \(u\). The paper distinguishes a reasonable crossnorm (Definition 2.3) from an assignment of uniform crossnorms (Definition 2.4).</p>`,['definition-2-3','definition-2-4','uniform-tensor']);
      note('evaluation-map','Evaluation at k','definition-3-1',t`\[\pi_k:C(M,X)\to X,\qquad\pi_k(g)=g(k).\]<p>It reads the value of an \(X\)-valued continuous function at \(k\).</p>`);
      note('tensor-inclusion','Inclusion at e','definition-3-1',t`\[\iota_e:X\to E\hat\otimes_\alpha X,\qquad\iota_e(x)=e\otimes x.\]<p>It fixes the first tensor factor at \(e\).</p>`);
      note('coordinate-operator','A coordinate of T','definition-3-2',t`\[T_{e,k}=\pi_kT\iota_e:X\to X.\]<p>Fix the first tensor factor at \(e\), apply \(T\), and evaluate at \(k\). Its decomposition is \(T_{e,k}=\lambda_{e,k}I+S_{e,k}\), with \(S_{e,k}\) of separable range.</p>`,['evaluation-map','tensor-inclusion']);
    }
  }
}

export function activateFormulaReferences(root,entries){
  const ns='http://www.w3.org/2000/svg';
  for(const term of root.querySelectorAll('svg .reading-formula-token')){
    if(term.dataset.readingRef)continue;
    const key=[...term.classList].find(c=>c.startsWith('formula-ref-'))?.slice(12);
    const entry=entries.get(key);if(!entry)continue;
    // MathJax normally hides the visual SVG from assistive technology. Expose
    // these buttons as a group while retaining its full accessible MathML.
    let svg=term.ownerSVGElement;while(svg.ownerSVGElement)svg=svg.ownerSVGElement;
    svg.removeAttribute('aria-hidden');svg.setAttribute('role','group');
    svg.setAttribute('aria-label','Definitions in this formula');
    term.dataset.readingRef=key;term.setAttribute('role','button');term.setAttribute('tabindex','0');
    term.setAttribute('aria-label',entry.title+' — show definition');
    term.setAttribute('aria-haspopup','dialog');term.setAttribute('aria-controls','reading-preview');term.setAttribute('aria-expanded','false');
    // A transparent rectangle makes the gaps between glyphs part of the term.
    // It is inserted before the glyphs so an inner term keeps its own reminder.
    const box=term.getBBox();
    const hit=document.createElementNS(ns,'rect');hit.setAttribute('x',box.x);hit.setAttribute('y',box.y);
    hit.setAttribute('width',box.width);hit.setAttribute('height',box.height);hit.setAttribute('class','formula-hit');
    hit.setAttribute('aria-hidden','true');term.prepend(hit);
    const line=document.createElementNS(ns,'line');line.setAttribute('x1',box.x);line.setAttribute('x2',box.x+box.width);
    line.setAttribute('y1',box.y-35);line.setAttribute('y2',box.y-35);
    line.setAttribute('class','formula-reminder-line');line.setAttribute('aria-hidden','true');term.append(line);
  }
}
