import Sigma.ComplexProjection
import Sigma.Splitting
import Mathlib.Analysis.Normed.Operator.Prod

/-! The actual ComplexJL(A) ⊕ Y decomposition for a family of split cylinders. -/
noncomputable section
namespace SigmaNonprimarity

theorem complexCharacteristic_mem_ComplexJL {B : Set (Set Point)} {b : Set Point} (hb : b ∈ B) :
    complexCharacteristic b ∈ ComplexJL B :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inl (Or.inr ⟨b, hb, rfl⟩)))

theorem complexConstant_mem_ComplexJL (B : Set (Set Point)) : complexCharacteristic Set.univ ∈ ComplexJL B :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inr rfl))

theorem complexCharacteristic_mem_ComplexCylinderJL {A : Set (Set Point)} {a : Set Point} (ha : a ∈ A) :
    complexCharacteristic a ∈ ComplexCylinderJL A :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inl (Or.inr ⟨a, ha, rfl⟩)))

theorem complexConstant_mem_ComplexCylinderJL (A : Set (Set Point)) :
    complexCharacteristic Set.univ ∈ ComplexCylinderJL A :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inr rfl))

theorem complexCharacteristic_fibre_mem_ComplexCylinderJL (A : Set (Set Point)) (n : ℕ) :
    complexCharacteristic (cylinder {n}) ∈ ComplexCylinderJL A :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inl (Or.inl ⟨n, rfl⟩)))

theorem complexCharacteristic_partition {s t : Set Point} (h : t ⊆ s) :
    complexCharacteristic s = complexCharacteristic t + complexCharacteristic (s \ t) := by
  classical
  ext p
  by_cases ht : p ∈ t
  · simp [ht, h ht]
  · by_cases hs : p ∈ s <;> simp [ht, hs]

theorem complexCharacteristic_fibre (n : ℕ) :
    complexCharacteristic (cylinder {n}) = complexCharacteristic {(n, false)} + complexCharacteristic {(n, true)} := by
  classical
  ext ⟨k, c⟩
  cases c <;> by_cases h : k = n <;> simp [cylinder, h]

theorem complexAverage_complexCharacteristic_cylinder (s : Set ℕ) :
    complexAverage (complexCharacteristic (cylinder s)) = complexCharacteristic (cylinder s) := by
  apply (complexAverage_eq_self_iff _).mpr
  intro n
  rfl

theorem complexAverage_complexCharacteristic_univ :
    complexAverage (complexCharacteristic Set.univ) = complexCharacteristic Set.univ := by
  apply (complexAverage_eq_self_iff _).mpr
  intro n
  simp

theorem complexAverage_complexCharacteristic_singleton (p : Point) :
    complexAverage (complexCharacteristic {p}) = (1 / 2 : ℂ) • complexCharacteristic (cylinder {p.1}) := by
  classical
  rcases p with ⟨n, c⟩
  ext ⟨k, d⟩
  cases c <;> cases d <;> by_cases h : k = n <;> simp [cylinder, h]

theorem complexAverage_complexCharacteristic_split {s : Set ℕ} {b : Set Point} (h : Splits s b) :
    complexAverage (complexCharacteristic b) = (1 / 2 : ℂ) • complexCharacteristic (cylinder s) := by
  classical
  ext ⟨n, c⟩
  by_cases hn : n ∈ s
  · have hi := h.2 n hn
    by_cases hf : (n, false) ∈ b
    · have ht : (n, true) ∉ b := hi.mp hf
      cases c <;> simp [cylinder, hn, hf, ht]
    · have ht : (n, true) ∈ b := Classical.not_not.mp (fun ht => hf (hi.mpr ht))
      cases c <;> simp [cylinder, hn, hf, ht]
  · have hb (d : Bool) : (n, d) ∉ b := fun hd => hn (h.1 hd)
    cases c <;> simp [cylinder, hn, hb]

theorem complexAverage_complexCharacteristic_other_split {s : Set ℕ} {b : Set Point} (h : Splits s b) :
    complexAverage (complexCharacteristic (cylinder s \ b)) =
      (1 / 2 : ℂ) • complexCharacteristic (cylinder s) := by
  have heq := complexCharacteristic_partition h.1
  have hp := congrArg complexAverage heq
  rw [map_add, complexAverage_complexCharacteristic_cylinder, complexAverage_complexCharacteristic_split h] at hp
  have hc : complexCharacteristic (cylinder s) =
      (1 / 2 : ℂ) • complexCharacteristic (cylinder s) +
      (1 / 2 : ℂ) • complexCharacteristic (cylinder s) := by
    rw [← add_smul]
    norm_num
  exact add_left_cancel (hp.symm.trans hc)

theorem complexCylinderJL_le_complexSplitJL {ι : Type*} (J : ι → Set ℕ) (b : ι → Set Point)
    (h : ∀ i, Splits (J i) (b i)) : ComplexCylinderJL (cylinderFamily J) ≤ ComplexJL (splitFamily J b) := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    intro f hf
    rcases hf with (⟨n, rfl⟩ | ⟨a, ⟨i, rfl⟩, rfl⟩) | rfl
    · rw [complexCharacteristic_fibre]
      exact (ComplexJL _).add_mem (complexCharacteristic_singleton_mem_ComplexJL _ _)
        (complexCharacteristic_singleton_mem_ComplexJL _ _)
    · rw [complexCharacteristic_partition (h i).1]
      exact (ComplexJL _).add_mem (complexCharacteristic_mem_ComplexJL (Or.inl ⟨i, rfl⟩))
        (complexCharacteristic_mem_ComplexJL (Or.inr ⟨i, rfl⟩))
    · exact complexConstant_mem_ComplexJL _
  · exact Submodule.isClosed_topologicalClosure _

theorem complexAverage_mem_complexCylinderJL {ι : Type*} (J : ι → Set ℕ) (b : ι → Set Point)
    (h : ∀ i, Splits (J i) (b i)) {f : ComplexAmbient} (hf : f ∈ ComplexJL (splitFamily J b)) :
    complexAverage f ∈ ComplexCylinderJL (cylinderFamily J) := by
  have hle : ComplexJL (splitFamily J b) ≤
      (ComplexCylinderJL (cylinderFamily J)).comap complexAverage.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro g hg
      change complexAverage g ∈ ComplexCylinderJL (cylinderFamily J)
      rcases hg with (⟨p, rfl⟩ | ⟨a, ha, rfl⟩) | rfl
      · rw [complexAverage_complexCharacteristic_singleton]
        exact (ComplexCylinderJL _).smul_mem _ (complexCharacteristic_fibre_mem_ComplexCylinderJL _ _)
      · rcases ha with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · rw [complexAverage_complexCharacteristic_split (h i)]
          exact (ComplexCylinderJL _).smul_mem _ (complexCharacteristic_mem_ComplexCylinderJL ⟨i, rfl⟩)
        · rw [complexAverage_complexCharacteristic_other_split (h i)]
          exact (ComplexCylinderJL _).smul_mem _ (complexCharacteristic_mem_ComplexCylinderJL ⟨i, rfl⟩)
      · rw [complexAverage_complexCharacteristic_univ]
        exact complexConstant_mem_ComplexCylinderJL _
    · exact (Submodule.isClosed_topologicalClosure _).preimage complexAverage.continuous
  exact hle hf

theorem complexAverage_eq_self_of_mem_complexCylinderJL {ι : Type*} (J : ι → Set ℕ)
    {f : ComplexAmbient} (hf : f ∈ ComplexCylinderJL (cylinderFamily J)) : complexAverage f = f := by
  have hle : ComplexCylinderJL (cylinderFamily J) ≤
      LinearMap.ker (complexAverage - ContinuousLinearMap.id ℂ ComplexAmbient).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro g hg
      change complexAverage g - g = 0
      apply sub_eq_zero.mpr
      rcases hg with (⟨n, rfl⟩ | ⟨a, ⟨i, rfl⟩, rfl⟩) | rfl
      · exact complexAverage_complexCharacteristic_cylinder _
      · exact complexAverage_complexCharacteristic_cylinder _
      · exact complexAverage_complexCharacteristic_univ
    · exact isClosed_eq (complexAverage - ContinuousLinearMap.id ℂ ComplexAmbient).continuous continuous_const
  exact sub_eq_zero.mp (hle hf)

/-- The range and kernel in Section 3.3, with P and I-P as the forward map. -/
def complexSplitJLEquiv {ι : Type*} (J : ι → Set ℕ) (b : ι → Set Point)
    (h : ∀ i, Splits (J i) (b i)) :
    ComplexJL (splitFamily J b) ≃L[ℂ]
      ComplexCylinderJL (cylinderFamily J) × complexAntisymmetricJL (splitFamily J b) := by
  let A := ComplexCylinderJL (cylinderFamily J)
  let X := ComplexJL (splitFamily J b)
  let Y := complexAntisymmetricJL (splitFamily J b)
  have hincl : A ≤ X := complexCylinderJL_le_complexSplitJL J b h
  have hanti (f : X) : complexAntiAverage f.val ∈ Y :=
    ⟨X.sub_mem f.property (hincl (complexAverage_mem_complexCylinderJL J b h f.property)), complexAverage_complexAntiAverage f⟩
  let e : X ≃ₗ[ℂ] (A × Y) :=
    { toFun := fun f => (⟨complexAverage f.val, complexAverage_mem_complexCylinderJL J b h f.property⟩,
        ⟨complexAntiAverage f.val, hanti f⟩)
      invFun := fun g => ⟨g.1.val + g.2.val, X.add_mem (hincl g.1.property) g.2.property.1⟩
      left_inv := by intro f; apply Subtype.ext; exact complexAverage_add_complexAntiAverage f.val
      right_inv := by
        intro g
        have hzero : complexAverage g.2.val = 0 := g.2.property.2
        apply Prod.ext <;> apply Subtype.ext
        · change complexAverage (g.1.val + g.2.val) = g.1.val
          rw [map_add, complexAverage_eq_self_of_mem_complexCylinderJL J g.1.property, hzero, add_zero]
        · change (g.1.val + g.2.val) - complexAverage (g.1.val + g.2.val) = g.2.val
          rw [map_add, complexAverage_eq_self_of_mem_complexCylinderJL J g.1.property, hzero, add_zero]
          abel
      map_add' := by intro f g; apply Prod.ext <;> apply Subtype.ext <;> exact map_add _ _ _
      map_smul' := by intro r f; apply Prod.ext <;> apply Subtype.ext <;> exact map_smul _ _ _ }
  refine LinearEquiv.toContinuousLinearEquivOfBounds
    (E := X) (F := A × Y) (σ := RingHom.id ℂ) (σ₂₁ := RingHom.id ℂ) e 1 2 ?_ ?_
  · intro f
    change max ‖complexAverage f.val‖ ‖complexAntiAverage f.val‖ ≤ 1 * ‖f.val‖
    rw [one_mul]
    exact max_le (complexAverage_norm_le f.val) (complexAntiAverage_norm_le f.val)
  · intro g
    change ‖g.1.val + g.2.val‖ ≤ 2 * max ‖g.1.val‖ ‖g.2.val‖
    have h1 := le_max_left ‖g.1.val‖ ‖g.2.val‖
    have h2 := le_max_right ‖g.1.val‖ ‖g.2.val‖
    have h3 := norm_add_le g.1.val g.2.val
    linarith

end SigmaNonprimarity


