import Sigma.ComplexSelectedStage
import Sigma.ComplexSelectedInjection
import ThesisCommon.Analysis.SigmaComplexClosedSpanImage

/-! The simple projected generators with the distinguished pair removed.
Their span together with the distinguished split vector is dense. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

def ComplexEnumeratedConstruction.projectedSingleton (D : ComplexEnumeratedConstruction) (side copy : Bool) (p : Point) :
    ComplexFinalCandidate D side := D.crossedProjection side (D.sideInjection copy
      ⟨complexCharacteristic {p},complexCharacteristic_singleton_mem_ComplexJL _ p⟩)

def ComplexEnumeratedConstruction.projectedFamily (D : ComplexEnumeratedConstruction) (side copy : Bool)
    (q : ConstructionIndex × Bool) : ComplexFinalCandidate D side :=
  D.crossedProjection side (D.sideInjection copy
    ⟨complexCharacteristic (D.familyEquiv copy q).val,complexCharacteristic_mem_ComplexJL (D.familyEquiv copy q).property⟩)

def ComplexEnumeratedConstruction.projectedOne (D : ComplexEnumeratedConstruction) (side copy : Bool) :
    ComplexFinalCandidate D side := D.crossedProjection side (D.sideInjection copy
      ⟨complexCharacteristic Set.univ,complexConstant_mem_ComplexJL _⟩)

def ComplexEnumeratedConstruction.puncturedGenerators (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) : Set (ComplexFinalCandidate D side) :=
  {f | ∃ copy p, f = D.projectedSingleton side copy p} ∪
  {f | ∃ copy i bit, (copy ≠ side ∨ i ≠ a) ∧ f = D.projectedFamily side copy (i,bit)} ∪
  {f | ∃ copy, f = D.projectedOne side copy}

def ComplexEnumeratedConstruction.puncturedSpan (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) : Submodule ℂ (ComplexFinalCandidate D side) :=
  Submodule.span ℂ (D.puncturedGenerators side a)

theorem ComplexEnumeratedConstruction.projectedFamily_selected (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (bit : Bool) : D.projectedFamily side side (a,bit) =
      (if bit then (-1/2 : ℂ) else 1/2) • D.distinguishedVector side a := by
  unfold ComplexEnumeratedConstruction.projectedFamily
  rw [D.crossedProjection_injection]
  apply Prod.ext <;> apply Subtype.ext
  · ext p
    change (0 : ℂ) = _ * 0
    simp
  · cases bit
    · exact complexAntiAverage_complexCharacteristic_split (D.splits side a)
    · exact complexAntiAverage_complexCharacteristic_other_split (D.splits side a)

def complexSelectedJLGenerators (B : Set (Set Point)) : Set ComplexAmbient :=
  {f | ∃ p : Point, f = complexCharacteristic {p}} ∪
    complexCharacteristic '' B ∪ {complexCharacteristic Set.univ}

theorem complex_jl_map_mem_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {B : Set (Set Point)} (φ : ComplexJL B →L[ℂ] E) (M : Submodule ℂ E) (hM : IsClosed (M : Set E))
    (hp : ∀ p, φ ⟨complexCharacteristic {p},complexCharacteristic_singleton_mem_ComplexJL B p⟩ ∈ M)
    (hb : ∀ b : B, φ ⟨complexCharacteristic b.val,complexCharacteristic_mem_ComplexJL b.property⟩ ∈ M)
    (h1 : φ ⟨complexCharacteristic Set.univ,complexConstant_mem_ComplexJL B⟩ ∈ M) (f : ComplexJL B) : φ f ∈ M := by
  apply ThesisCommon.complexClosedSpan_map_mem (complexSelectedJLGenerators B) φ M hM ?_ f
  rintro x ((⟨p,rfl⟩ | ⟨b,hb',rfl⟩) | rfl)
  · exact hp p
  · exact hb ⟨b,hb'⟩
  · exact h1

theorem ComplexEnumeratedConstruction.punctured_generators_dense (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (f : ComplexFinalCandidate D side) :
    f ∈ (Submodule.span ℂ (insert (D.distinguishedVector side a) (D.puncturedGenerators side a))).topologicalClosure := by
  classical
  let M := Submodule.span ℂ (insert (D.distinguishedVector side a) (D.puncturedGenerators side a))
  have hgen {g : ComplexFinalCandidate D side} (hg : g ∈ D.puncturedGenerators side a) : g ∈ M :=
    Submodule.subset_span (Set.mem_insert_of_mem _ hg)
  have hphi (copy : Bool) (g : ComplexJL (D.family copy)) :
      D.crossedProjection side (D.sideInjection copy g) ∈ M.topologicalClosure := by
    apply complex_jl_map_mem_closed ((D.crossedProjection side).comp (D.sideInjection copy))
      M.topologicalClosure (Submodule.isClosed_topologicalClosure _) ?_ ?_ ?_ g
    · intro p
      exact Submodule.le_topologicalClosure _ (hgen (Or.inl (Or.inl ⟨copy,p,rfl⟩)))
    · intro b
      obtain ⟨⟨i,bit⟩,rfl⟩ := (D.familyEquiv copy).surjective b
      apply Submodule.le_topologicalClosure
      by_cases hc : copy = side
      · by_cases hi : i = a
        · subst copy i
          change D.projectedFamily side side (a,bit) ∈ M
          rw [D.projectedFamily_selected]
          exact M.smul_mem _ (Submodule.subset_span (Set.mem_insert _ _))
        · exact hgen (Or.inl (Or.inr ⟨copy,i,bit,Or.inr hi,rfl⟩))
      · exact hgen (Or.inl (Or.inr ⟨copy,i,bit,Or.inl hc,rfl⟩))
    · exact Submodule.le_topologicalClosure _ (hgen (Or.inr ⟨copy,rfl⟩))
  obtain ⟨g,rfl⟩ := D.crossedProjection_surjective side f
  have hg : g = D.sideInjection false g.1 + D.sideInjection true g.2 := by
    apply Prod.ext <;> simp [ComplexEnumeratedConstruction.sideInjection]
  rw [hg,map_add]
  exact M.topologicalClosure.add_mem (hphi false g.1) (hphi true g.2)

theorem ComplexEnumeratedConstruction.distinguished_approximation (D : ComplexEnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (g : ComplexFinalCandidate D side) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (r : ℂ) (s : ComplexFinalCandidate D side), s ∈ D.puncturedSpan side a ∧
      ‖g - (r • D.distinguishedVector side a + s)‖ < δ := by
  have hd := D.punctured_generators_dense side a g
  obtain ⟨x,hx,hgx⟩ := Metric.mem_closure_iff.mp hd δ hδ
  obtain ⟨r,s,hs,rfl⟩ := Submodule.mem_span_insert.mp hx
  exact ⟨r,s,hs,by simpa only [dist_eq_norm] using hgx⟩

end SigmaNonprimarity


