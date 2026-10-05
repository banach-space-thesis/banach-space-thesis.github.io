// Explanations belong to a particular article; shared numbering is not a correspondence.
const t=String.raw;
export function paperNotation(paper,tex){
  if(paper==='pems'){
    if(tex==='AL')return 'al-space';
    if(/^m\(TV?\)$/.test(tex))return 'minimum-modulus';
    if(/^\\lVert T(?:\^\{?\*\}?)?\\rVert_\{?w\}?$/.test(tex))return 'weak-essential-norm';
  }
  if(paper==='sigma'&&/^(?:\\mathrm\{DP\}|\\text\{DP\}|DP)$/.test(tex))return 'definition-3-3';
}
export const paperNotes={
  pems:{
    'theorem-1-1':{
      idea:t`<p>The weak essential norm measures how far an operator is from being weakly compact. This theorem says that a nearest weakly compact operator actually exists for the L¹ spaces considered here. It also expresses that distance using restrictions to small measurable sets and the part outside a set of finite measure.</p>`,
      notation:[[t`\(\|T\|_w\)`,'The distance from T to the weakly compact operators.'],[t`\(\Theta\)`,'A measurable part of the range measure space with finite measure.'],[t`\(\alpha_\Theta(T)\)`,'The quantity measuring concentration on small subsets of Θ together with the part outside Θ.']],
      steps:[['What an infimum alone says',t`<p>The definition gives weakly compact operators whose distances from \(T\) approach \(\|T\|_w\). It does not, by itself, give an operator at exactly that distance.</p>`],['What the theorem adds',t`<p>There is one weakly compact \(W\) satisfying \(\|T-W\|=\|T\|_w\). This is attainment of the infimum.</p>`],['How the formula helps',t`<p>The second equality computes the same distance through measurable restrictions. Thus estimates on \(\alpha_\Theta(T)\) become estimates on the distance to weak compactness.</p>`]],
      uses:['weak-essential-norm','definition-3-3'],basis:'An explanation of the statement of Theorem 1.1, not a replacement for its proof in Section 4.'
    },
    'theorem-1-4':{
      idea:t`<p>A non-weakly compact operator between AL-spaces contains enough of ℓ¹ to recover its identity. The theorem measures how efficiently this can be done: the best reciprocal product of the two surrounding operator norms is exactly the weak essential norm.</p>`,
      notation:[[t`\(V:\ell_1\to E\)`,'The first map into the domain of T.'],[t`\(U:F\to\ell_1\)`,'The map that recovers the original ℓ¹ vector after applying T.'],[t`\(UTV=I_{\ell_1}\)`,'Every ℓ¹ vector is recovered exactly.']],
      steps:[['Read the maps in order',t`<p>A vector travels through \(\ell_1\xrightarrow{V}E\xrightarrow{T}F\xrightarrow{U}\ell_1\). The composition is the identity.</p>`],['Why weak compactness prevents this',t`<p>If \(T\) were weakly compact, its composition with bounded linear maps would be weakly compact. The identity on the nonreflexive space \(\ell_1\) is not weakly compact.</p>`],['Read the quantitative conclusion',t`<p>A smaller product \(\|U\|\|V\|\) gives a larger reciprocal. Taking the supremum over all such factorisations gives exactly \(\|T\|_w\).</p>`]],
      uses:['al-space','weak-essential-norm'],basis:'Theorem 1.4 and the discussion preceding it.'
    },
    'theorem-1-5':{
      idea:t`<p>The first equality measures how well T preserves a copy of c₀, using the minimum modulus of TV. The additional hypotheses in the later clauses allow this lower bound to be expressed by an exact identity factorisation.</p>`,
      notation:[[t`\(m(TV)\)`,'The infimum of ‖TVx‖ over unit vectors x in c₀.'],[t`\(\|V\|\leq1\)`,'The first map is normalized so its scale cannot artificially enlarge the bound.'],[t`\(\|T^*\|_w\)`,'The weak essential norm of the adjoint, which need not be replaced by ‖T‖w without justification.']],
      steps:[['Start with the first clause',t`<p>Only compact Hausdorff spaces are required for the formula involving \(m(TV)\).</p>`],['Check the hypothesis on K',t`<p>Sequential compactness of \(K\) gives the identity factorisation through \(c_0\) in the next clause.</p>`],['Check the hypothesis on L',t`<p>Extreme disconnectedness of \(L\) gives the corresponding \(\ell_\infty\) factorisation in the last clause. Keep the two compact spaces and their roles distinct.</p>`]],
      uses:['minimum-modulus','weak-essential-norm','corollary-1-2'],basis:'The three clauses of Theorem 1.5.'
    }
  },
  sigma:{
    'theorem-1-1':{
      idea:t`<p>To show that a class is not primary, it suffices to split one of its members into two summands, neither of which belongs to the class up to isomorphism. Here that member is a C(L)-space. The construction arranges that both summands satisfy DP, which obstructs their being Banach lattices by Proposition 3.4.</p>`,
      notation:[[t`\(C(L)\simeq X\oplus\widetilde X\)`,'A Banach-space isomorphism with a direct sum of two closed summands.'],[t`\(\mathrm{DP}\)`,'The obstruction to simultaneously realizing coordinatewise absolute values for every norming sequence.'],[t`\(K_{\mathcal B}\)`,'The compactification associated with an almost disjoint family; its point at infinity also contributes to the dual.']],
      steps:[['Build the two decompositions',t`<p>The averaging projection separates functions that are constant on each two-point fibre from the antisymmetric functions. Apply this to each of two constructed families.</p>`],['Cross the summands',t`<p>Regroup the two decompositions, pairing the symmetric part of one with the antisymmetric part of the other. Both crossed spaces still form a direct-sum decomposition of a C(L)-space.</p>`],['Exclude lattice representations',t`<p>The construction gives DP for both crossed spaces, together with a countable norming set and an ℓ¹ dual. Proposition 3.4 then excludes isomorphism to any Banach lattice.</p>`],['Read the formal correspondence',t`<p>The Lean proof retains the two atoms at infinity throughout the dual representation and the construction. They cannot both be discarded from the printed coordinates. The corrected norming inequality and the corrected error estimate in Section 6 are used as well.</p>`]],
      uses:['primary-class','definition-3-3','proposition-3-4','proposition-4-4'],basis:'Sections 2–6, thesis Proposition 6.7, and the formalisation’s documented corrections D01–D03 and D06.'
    },
    'proposition-4-4':{
      idea:t`<p>Nonseparation must survive every stage of the construction. The proposition as printed preserves it after adjoining one set. The stage algebra, however, contains both halves of a split.</p><p>Thesis Proposition 6.7 proves the stronger selection needed here: choose one supporting set \(C\) so that adjoining \(Z\) and \(C\setminus Z\) preserves every listed nonseparation, for every \(Z\subseteq C\). Lean proves and uses this strengthening. The main theorem is unchanged.</p>`,
      notation:[[t`\(\mathfrak B_i[Z,C\setminus Z]\)`,'The Boolean algebra generated by the old algebra and both halves of the split.'],[t`\(\exists C\in\mathcal C\;\forall Z\subseteq C\;\forall i\in I\)`,'One supporting set works for every split and every pair under consideration.']],
      steps:[['Why one set is insufficient',t`<p>Adjoining \(Z\) gives its complement in the whole base, but need not give \(C\setminus Z\): the old algebra need not contain \(C\). Enlarging the algebra further could introduce separating tests.</p>`],['Keep the old sets outside C',t`<p>Every set in the enlarged algebra agrees outside \(C\) with a member of the old algebra. Inside \(C\), the stronger argument permits arbitrary subsets.</p>`],['Apply the counting argument',t`<p>Fix the old sets outside \(C\), the tests from the other algebra, and a positive rational separation constant. The finite-variation estimate allows only finitely many almost-disjoint supporting sets with these same separating choices. There are fewer than continuum many such choices, so some supporting set preserves all the required nonseparations.</p>`],['Use the stronger statement in the recursion',t`<p>Apply the selection on each copy, preserving the new pairs from the first choice when making the second. This justifies adjoining both halves at each successor stage.</p>`]],
      uses:['definition-4-1','lemma-4-5','theorem-1-1'],basis:'Thesis Proposition 6.7 and its proof; D06 in the formal correspondence; Lean LocalizedSelection, SplitSelection and TwoSidedSuccessor.'
    },
    'definition-3-2':{
      idea:t`<p>A norming sequence detects the size of every vector up to a fixed positive factor. No nonzero vector can be invisible to all the functionals.</p><p>The arXiv inequality is reversed. This edition uses the lower bound required by the argument and used in Lean.</p>`,
      notation:[[t`\(e_n^*\in B_{X^*}\)`,'Each functional has norm at most one.'],[t`\(0<c\leq1\)`,'The same positive constant works for every vector.'],[t`\(c\|x\|\leq\sup_n|e_n^*(x)|\leq\|x\|\)`,'Together, these bounds show that the evaluations measure an equivalent norm.']],
      steps:[['The upper bound is automatic',t`<p>Since \(\|e_n^*\|\leq1\), every evaluation satisfies \(|e_n^*(x)|\leq\|x\|\).</p>`],['The lower bound carries the content',t`<p>The supremum must be at least \(c\|x\|\), uniformly in \(x\). In particular, if all evaluations vanish then \(x=0\).</p>`],['Why the printed inequality fails',t`<p>The zero sequence satisfies \(\|x\|\geq c\sup_n|e_n^*(x)|\) for every \(x\), but detects no vector. That inequality cannot express the norming property needed here.</p>`]],
      uses:['definition-3-3'],basis:'Definition 3.2; correction D01 in the formal correspondence.'
    },
    'definition-3-3':{
      idea:t`<p>Fix a norming sequence and look at the coordinates it assigns to a vector. DP says that, for some vector, taking the absolute value of every coordinate cannot be achieved by another vector of the space. This failure must occur for every norming sequence.</p>`,
      notation:[[t`\(f\)`,'A vector whose absolute coordinate values cannot all be realized.'],[t`\(g\)`,'A possible vector realizing those absolute values. DP excludes all such g for a suitable f.'],[t`\(e_n^*(g)=|e_n^*(f)|\)`,'The coordinate identity that would have to hold for every n.']],
      steps:[['Choose any norming sequence',t`<p>The first quantifier is universal. Finding one inconvenient choice of coordinates does not establish DP.</p>`],['Find a vector for that sequence',t`<p>The vector \(f\) may depend on the sequence. It must defeat every candidate \(g\).</p>`],['Use the obstruction',t`<p>Under the additional hypotheses of Proposition 3.4, DP is equivalent to failure of a Banach-lattice representation.</p>`]],
      uses:['definition-3-2','proposition-3-4'],basis:'Definition 3.3 and Proposition 3.4.'
    }
  }
};
paperNotes.sigma['theorem-1-1'].steps.splice(1,0,['Preserve nonseparation after both halves are adjoined',t`<p>The construction needs a stronger form of Proposition 4.4 than the one printed in the article. Nonseparation must survive adjoining both \(Z\) and \(C\setminus Z\). Thesis Proposition 6.7 fills this omission, and Lean proves and uses the stronger selection. This repairs the argument without weakening the main conclusion.</p>`]);

export function addPaperGlossary(id,{definition,glossary,paper}){
  addRemainingGlossary(id,{definition,glossary,paper});
  function prose(key,title,target,html,pattern){
    const paragraph=document.getElementById(target);
    if(!paragraph||!paper.contains(paragraph))throw Error('Missing definition passage: '+target);
    glossary(key,title,'Definition in the paper',target,html,pattern,paragraph.outerHTML);
  }
  if(id==='pems'){
    definition('definition-3-3','Strictly localizable measure space','strictly\\s+localizable|decomposable');
    definition('definition-3-4','Measure algebra','measure\\s+algebras?');
    definition('definition-3-6','Countably generated σ-algebra','countably\\s+generated');
    definition('definition-3-11','Integral operator','integral\\s+operators?');
    definition('definition-3-16','Modulus of equi-integrability','modulus\\s+of\\s+equi-integrability');
    definition('definition-4-5','Rich family','rich\\s+famil(?:y|ies)');
    definition('definition-5-4','Disjoint and almost disjoint sequences','(?:almost\\s+)?disjoint\\s+sequences?');
    definition('definition-5-8','Measure of weak noncompactness','(?:normalized\\s+|normalised\\s+)?measures?\\s+of\\s+weak\\s+noncompactness');
    definition('definition-6-1','Modulus of uniform regularity','modulus\\s+of\\s+uniform\\s+regularity');
    prose('al-space','AL-space','S1.p1',t`<p>A Banach lattice whose norm is additive on the positive cone:</p>\[\|x+y\|=\|x\|+\|y\|\quad(x,y\geq0).\]<p>This is the abstract form of the familiar additivity for nonnegative L¹ functions.</p>`,'AL[-– ]spaces?');
    prose('weak-essential-norm','Weak essential norm','S1.p3',t`<p>The distance from a bounded linear map to the weakly compact operators:</p>\[\|T\|_w=\inf_{W\in\mathscr W(E,F)}\|T-W\|.\]<p>The dual weak essential norm is the same quantity for the adjoint \(T^*\).</p>`,'(?:dual\\s+)?weak\\s+essential\\s+norms?');
    prose('minimum-modulus','Minimum modulus','S1.p10',t`\[m(T)=\inf_{\|x\|=1}\|Tx\|.\]<p>A positive minimum modulus means that T is bounded below: it does not make unit vectors arbitrarily small.</p>`,'minimum\\s+modulus|injectivity\\s+modulus');
    prose('bonsall','Bonsall’s minimality property','S1.p15',t`<p>An algebra norm \(p\) has this property when every algebra norm \(q\) satisfying \(q(a)\leq p(a)\) for all \(a\) is equal to \(p\). The conclusion is equality, not merely equivalence of norms.</p>`,"Bonsall['’]s\\s+minimality\\s+property");
  }else if(id==='sigma'){
    definition('definition-3-2','Norming sequence','(?:c[-– ])?norming\\s+(?:sequences?|sets?)');
    definition('definition-3-3','Desired Property (DP)','Desired\\s+Property(?:\\s+of\\s+De\\s+Hevia[^,.]*Tradacete)?|DP');
    definition('definition-4-1','Separation by Boolean algebras',null);
    definition('definition-4-6','Admissible sequence','admissible(?:\\s+sequences?)?');
    prose('almost-disjoint','Almost disjoint family','S3.SS1.p2',t`<p>A family of infinite sets is almost disjoint when any two distinct members have finite intersection. Each set is infinite; only their pairwise overlaps are finite.</p>`,'almost\\s+disjoint(?:\\s+famil(?:y|ies))?');
    prose('primary-class','Primary class','S1.p2',t`<p>A class of Banach spaces, understood up to isomorphism, is primary if every decomposition \(E\simeq X\oplus Y\) of a member E has at least one summand isomorphic to a member of that class.</p><p>This differs from asking whether one particular Banach space is primary.</p>`,'primary');
  }
}
import {remainingNotes,addRemainingGlossary} from './remaining-notes.js';
Object.assign(paperNotes,remainingNotes);
