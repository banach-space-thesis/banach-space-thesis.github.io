import Sigma.Projection
import Mathlib.Analysis.Normed.Operator.Prod

/-! The actual JL(A) ⊕ Y decomposition for a family of split cylinders. -/
noncomputable section
namespace SigmaNonprimarity

def cylinderFamily {ι : Type*} (J : ι → Set ℕ) : Set (Set Point) :=
  Set.range (fun i => cylinder (J i))

def splitFamily {ι : Type*} (J : ι → Set ℕ) (b : ι → Set Point) : Set (Set Point) :=
  Set.range b ∪ Set.range (fun i => cylinder (J i) \ b i)

theorem characteristic_mem_JL {B : Set (Set Point)} {b : Set Point} (hb : b ∈ B) :
    characteristic b ∈ JL B :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inl (Or.inr ⟨b, hb, rfl⟩)))

theorem constant_mem_JL (B : Set (Set Point)) : characteristic Set.univ ∈ JL B :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inr rfl))

theorem characteristic_mem_CylinderJL {A : Set (Set Point)} {a : Set Point} (ha : a ∈ A) :
    characteristic a ∈ CylinderJL A :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inl (Or.inr ⟨a, ha, rfl⟩)))

theorem constant_mem_CylinderJL (A : Set (Set Point)) :
    characteristic Set.univ ∈ CylinderJL A :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inr rfl))

theorem characteristic_fibre_mem_CylinderJL (A : Set (Set Point)) (n : ℕ) :
    characteristic (cylinder {n}) ∈ CylinderJL A :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inl (Or.inl ⟨n, rfl⟩)))

theorem characteristic_partition {s t : Set Point} (h : t ⊆ s) :
    characteristic s = characteristic t + characteristic (s \ t) := by
  classical
  ext p
  by_cases ht : p ∈ t
  · simp [ht, h ht]
  · by_cases hs : p ∈ s <;> simp [ht, hs]

theorem characteristic_fibre (n : ℕ) :
    characteristic (cylinder {n}) = characteristic {(n, false)} + characteristic {(n, true)} := by
  classical
  ext ⟨k, c⟩
  cases c <;> by_cases h : k = n <;> simp [cylinder, h]

theorem average_characteristic_cylinder (s : Set ℕ) :
    average (characteristic (cylinder s)) = characteristic (cylinder s) := by
  apply (average_eq_self_iff _).mpr
  intro n
  rfl

theorem average_characteristic_univ :
    average (characteristic Set.univ) = characteristic Set.univ := by
  apply (average_eq_self_iff _).mpr
  intro n
  simp

theorem average_characteristic_singleton (p : Point) :
    average (characteristic {p}) = (1 / 2 : ℝ) • characteristic (cylinder {p.1}) := by
  classical
  rcases p with ⟨n, c⟩
  ext ⟨k, d⟩
  cases c <;> cases d <;> by_cases h : k = n <;> simp [cylinder, h]

theorem average_characteristic_split {s : Set ℕ} {b : Set Point} (h : Splits s b) :
    average (characteristic b) = (1 / 2 : ℝ) • characteristic (cylinder s) := by
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

theorem average_characteristic_other_split {s : Set ℕ} {b : Set Point} (h : Splits s b) :
    average (characteristic (cylinder s \ b)) =
      (1 / 2 : ℝ) • characteristic (cylinder s) := by
  have heq := characteristic_partition h.1
  have hp := congrArg average heq
  rw [map_add, average_characteristic_cylinder, average_characteristic_split h] at hp
  have hc : characteristic (cylinder s) =
      (1 / 2 : ℝ) • characteristic (cylinder s) +
      (1 / 2 : ℝ) • characteristic (cylinder s) := by
    rw [← add_smul]
    norm_num
  exact add_left_cancel (hp.symm.trans hc)

theorem cylinderJL_le_splitJL {ι : Type*} (J : ι → Set ℕ) (b : ι → Set Point)
    (h : ∀ i, Splits (J i) (b i)) : CylinderJL (cylinderFamily J) ≤ JL (splitFamily J b) := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    intro f hf
    rcases hf with (⟨n, rfl⟩ | ⟨a, ⟨i, rfl⟩, rfl⟩) | rfl
    · rw [characteristic_fibre]
      exact (JL _).add_mem (characteristic_singleton_mem_JL _ _)
        (characteristic_singleton_mem_JL _ _)
    · rw [characteristic_partition (h i).1]
      exact (JL _).add_mem (characteristic_mem_JL (Or.inl ⟨i, rfl⟩))
        (characteristic_mem_JL (Or.inr ⟨i, rfl⟩))
    · exact constant_mem_JL _
  · exact Submodule.isClosed_topologicalClosure _

theorem average_mem_cylinderJL {ι : Type*} (J : ι → Set ℕ) (b : ι → Set Point)
    (h : ∀ i, Splits (J i) (b i)) {f : Ambient} (hf : f ∈ JL (splitFamily J b)) :
    average f ∈ CylinderJL (cylinderFamily J) := by
  have hle : JL (splitFamily J b) ≤
      (CylinderJL (cylinderFamily J)).comap average.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro g hg
      change average g ∈ CylinderJL (cylinderFamily J)
      rcases hg with (⟨p, rfl⟩ | ⟨a, ha, rfl⟩) | rfl
      · rw [average_characteristic_singleton]
        exact (CylinderJL _).smul_mem _ (characteristic_fibre_mem_CylinderJL _ _)
      · rcases ha with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · rw [average_characteristic_split (h i)]
          exact (CylinderJL _).smul_mem _ (characteristic_mem_CylinderJL ⟨i, rfl⟩)
        · rw [average_characteristic_other_split (h i)]
          exact (CylinderJL _).smul_mem _ (characteristic_mem_CylinderJL ⟨i, rfl⟩)
      · rw [average_characteristic_univ]
        exact constant_mem_CylinderJL _
    · exact (Submodule.isClosed_topologicalClosure _).preimage average.continuous
  exact hle hf

theorem average_eq_self_of_mem_cylinderJL {ι : Type*} (J : ι → Set ℕ)
    {f : Ambient} (hf : f ∈ CylinderJL (cylinderFamily J)) : average f = f := by
  have hle : CylinderJL (cylinderFamily J) ≤
      LinearMap.ker (average - ContinuousLinearMap.id ℝ Ambient).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro g hg
      change average g - g = 0
      apply sub_eq_zero.mpr
      rcases hg with (⟨n, rfl⟩ | ⟨a, ⟨i, rfl⟩, rfl⟩) | rfl
      · exact average_characteristic_cylinder _
      · exact average_characteristic_cylinder _
      · exact average_characteristic_univ
    · exact isClosed_eq (average - ContinuousLinearMap.id ℝ Ambient).continuous continuous_const
  exact sub_eq_zero.mp (hle hf)

/-- The range and kernel in Section 3.3, with P and I-P as the forward map. -/
def splitJLEquiv {ι : Type*} (J : ι → Set ℕ) (b : ι → Set Point)
    (h : ∀ i, Splits (J i) (b i)) :
    JL (splitFamily J b) ≃L[ℝ]
      CylinderJL (cylinderFamily J) × antisymmetricJL (splitFamily J b) := by
  let A := CylinderJL (cylinderFamily J)
  let X := JL (splitFamily J b)
  let Y := antisymmetricJL (splitFamily J b)
  have hincl : A ≤ X := cylinderJL_le_splitJL J b h
  have hanti (f : X) : antiAverage f.val ∈ Y :=
    ⟨X.sub_mem f.property (hincl (average_mem_cylinderJL J b h f.property)), average_antiAverage f⟩
  let e : X ≃ₗ[ℝ] (A × Y) :=
    { toFun := fun f => (⟨average f.val, average_mem_cylinderJL J b h f.property⟩,
        ⟨antiAverage f.val, hanti f⟩)
      invFun := fun g => ⟨g.1.val + g.2.val, X.add_mem (hincl g.1.property) g.2.property.1⟩
      left_inv := by intro f; apply Subtype.ext; exact average_add_antiAverage f.val
      right_inv := by
        intro g
        have hzero : average g.2.val = 0 := g.2.property.2
        apply Prod.ext <;> apply Subtype.ext
        · change average (g.1.val + g.2.val) = g.1.val
          rw [map_add, average_eq_self_of_mem_cylinderJL J g.1.property, hzero, add_zero]
        · change (g.1.val + g.2.val) - average (g.1.val + g.2.val) = g.2.val
          rw [map_add, average_eq_self_of_mem_cylinderJL J g.1.property, hzero, add_zero]
          abel
      map_add' := by intro f g; apply Prod.ext <;> apply Subtype.ext <;> exact map_add _ _ _
      map_smul' := by intro r f; apply Prod.ext <;> apply Subtype.ext <;> exact map_smul _ _ _ }
  refine LinearEquiv.toContinuousLinearEquivOfBounds
    (E := X) (F := A × Y) (σ := RingHom.id ℝ) (σ₂₁ := RingHom.id ℝ) e 1 2 ?_ ?_
  · intro f
    change max ‖average f.val‖ ‖antiAverage f.val‖ ≤ 1 * ‖f.val‖
    rw [one_mul]
    exact max_le (average_norm_le f.val) (antiAverage_norm_le f.val)
  · intro g
    change ‖g.1.val + g.2.val‖ ≤ 2 * max ‖g.1.val‖ ‖g.2.val‖
    have h1 := le_max_left ‖g.1.val‖ ‖g.2.val‖
    have h2 := le_max_right ‖g.1.val‖ ‖g.2.val‖
    have h3 := norm_add_le g.1.val g.2.val
    linarith

end SigmaNonprimarity
