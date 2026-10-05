import Sigma.SelectedStage
import Sigma.CrossedInjection
import ThesisCommon.Analysis.ClosedSpanImage

/-! The simple projected generators with the distinguished pair removed.
Their span together with the distinguished split vector is dense. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace
attribute [local instance] pairedJLGroup pairedJLSpace pairedJLDualGroup
attribute [local instance] finalCandidateGroup finalCandidateSpace

def EnumeratedConstruction.projectedSingleton (D : EnumeratedConstruction) (side copy : Bool) (p : Point) :
    FinalCandidate D side := D.crossedProjection side (D.sideInjection copy
      ⟨characteristic {p},characteristic_singleton_mem_JL _ p⟩)

def EnumeratedConstruction.projectedFamily (D : EnumeratedConstruction) (side copy : Bool)
    (q : ConstructionIndex × Bool) : FinalCandidate D side :=
  D.crossedProjection side (D.sideInjection copy
    ⟨characteristic (D.familyEquiv copy q).val,characteristic_mem_JL (D.familyEquiv copy q).property⟩)

def EnumeratedConstruction.projectedOne (D : EnumeratedConstruction) (side copy : Bool) :
    FinalCandidate D side := D.crossedProjection side (D.sideInjection copy
      ⟨characteristic Set.univ,constant_mem_JL _⟩)

def EnumeratedConstruction.puncturedGenerators (D : EnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) : Set (FinalCandidate D side) :=
  {f | ∃ copy p, f = D.projectedSingleton side copy p} ∪
  {f | ∃ copy i bit, (copy ≠ side ∨ i ≠ a) ∧ f = D.projectedFamily side copy (i,bit)} ∪
  {f | ∃ copy, f = D.projectedOne side copy}

def EnumeratedConstruction.puncturedSpan (D : EnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) : Submodule ℝ (FinalCandidate D side) :=
  Submodule.span ℝ (D.puncturedGenerators side a)

theorem EnumeratedConstruction.projectedFamily_selected (D : EnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (bit : Bool) : D.projectedFamily side side (a,bit) =
      (if bit then (-1/2 : ℝ) else 1/2) • D.distinguishedVector side a := by
  unfold EnumeratedConstruction.projectedFamily
  rw [D.crossedProjection_injection]
  apply Prod.ext <;> apply Subtype.ext
  · ext p
    change (0 : ℝ) = _ * 0
    simp
  · cases bit
    · exact antiAverage_characteristic_split (D.splits side a)
    · exact antiAverage_characteristic_other_split (D.splits side a)

theorem jl_map_mem_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Set (Set Point)} (φ : JL B →L[ℝ] E) (M : Submodule ℝ E) (hM : IsClosed (M : Set E))
    (hp : ∀ p, φ ⟨characteristic {p},characteristic_singleton_mem_JL B p⟩ ∈ M)
    (hb : ∀ b : B, φ ⟨characteristic b.val,characteristic_mem_JL b.property⟩ ∈ M)
    (h1 : φ ⟨characteristic Set.univ,constant_mem_JL B⟩ ∈ M) (f : JL B) : φ f ∈ M := by
  apply ThesisCommon.closedSpan_map_mem (jlGenerators B) φ M hM ?_ f
  rintro x ((⟨p,rfl⟩ | ⟨b,hb',rfl⟩) | rfl)
  · exact hp p
  · exact hb ⟨b,hb'⟩
  · exact h1

theorem EnumeratedConstruction.punctured_generators_dense (D : EnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (f : FinalCandidate D side) :
    f ∈ (Submodule.span ℝ (insert (D.distinguishedVector side a) (D.puncturedGenerators side a))).topologicalClosure := by
  classical
  let M := Submodule.span ℝ (insert (D.distinguishedVector side a) (D.puncturedGenerators side a))
  have hgen {g : FinalCandidate D side} (hg : g ∈ D.puncturedGenerators side a) : g ∈ M :=
    Submodule.subset_span (Set.mem_insert_of_mem _ hg)
  have hphi (copy : Bool) (g : JL (D.family copy)) :
      D.crossedProjection side (D.sideInjection copy g) ∈ M.topologicalClosure := by
    apply jl_map_mem_closed ((D.crossedProjection side).comp (D.sideInjection copy))
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
    apply Prod.ext <;> simp [EnumeratedConstruction.sideInjection]
  rw [hg,map_add]
  exact M.topologicalClosure.add_mem (hphi false g.1) (hphi true g.2)

theorem EnumeratedConstruction.distinguished_approximation (D : EnumeratedConstruction) (side : Bool)
    (a : ConstructionIndex) (g : FinalCandidate D side) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (r : ℝ) (s : FinalCandidate D side), s ∈ D.puncturedSpan side a ∧
      ‖g - (r • D.distinguishedVector side a + s)‖ < δ := by
  have hd := D.punctured_generators_dense side a g
  obtain ⟨x,hx,hgx⟩ := Metric.mem_closure_iff.mp hd δ hδ
  obtain ⟨r,s,hs,rfl⟩ := Submodule.mem_span_insert.mp hx
  exact ⟨r,s,hs,by simpa only [dist_eq_norm] using hgx⟩

end SigmaNonprimarity
