import Sigma.ContinuousRepresentation
import Sigma.Splitting
import Sigma.PointCoding

/-! The fibre-constant cylinder space is a genuine C(K) space. We relabel its
countable base by `pointCode`, keeping one base point for each whole fibre. -/
noncomputable section
open Set
namespace SigmaNonprimarity

def cylinderBaseFamily {I : Type*} (J : I → Set ℕ) : Set (Set Point) :=
  Set.range (fun i => pointCode ⁻¹' J i)

def compressCylinder : Ambient →L[ℝ] Ambient :=
  LinearMap.mkContinuous
    { toFun := fun f => BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
        (fun p => f (pointCode p, false)) ‖f‖ (fun p => f.norm_coe_le_norm _)
      map_add' := by intros; ext p; rfl
      map_smul' := by intros; ext p; rfl }
    1 (by
      intro f
      rw [one_mul]
      exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
        (fun p => f.norm_coe_le_norm _))

def expandCylinder : Ambient →L[ℝ] Ambient :=
  LinearMap.mkContinuous
    { toFun := fun f => BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
        (fun p => f (pointCode.symm p.1)) ‖f‖ (fun p => f.norm_coe_le_norm _)
      map_add' := by intros; ext p; rfl
      map_smul' := by intros; ext p; rfl }
    1 (by
      intro f
      rw [one_mul]
      exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
        (fun p => f.norm_coe_le_norm _))

@[simp] theorem compressCylinder_apply (f : Ambient) (p : Point) :
    compressCylinder f p = f (pointCode p, false) := rfl

@[simp] theorem expandCylinder_apply (f : Ambient) (p : Point) :
    expandCylinder f p = f (pointCode.symm p.1) := rfl

theorem compressCylinder_norm_le (f : Ambient) : ‖compressCylinder f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    (fun _ => f.norm_coe_le_norm _)

theorem expandCylinder_norm_le (f : Ambient) : ‖expandCylinder f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    (fun _ => f.norm_coe_le_norm _)

theorem compress_expandCylinder (f : Ambient) : compressCylinder (expandCylinder f) = f := by
  ext p
  simp

theorem expand_compressCylinder {I : Type*} (J : I → Set ℕ)
    {f : Ambient} (hf : f ∈ CylinderJL (cylinderFamily J)) :
    expandCylinder (compressCylinder f) = f := by
  have h := (average_eq_self_iff f).mp (average_eq_self_of_mem_cylinderJL J hf)
  ext ⟨n, b⟩
  cases b <;> simp [h]

theorem compressCylinder_characteristic (s : Set ℕ) :
    compressCylinder (characteristic (cylinder s)) = characteristic (pointCode ⁻¹' s) := by
  ext p
  rfl

theorem expandCylinder_characteristic (s : Set ℕ) :
    expandCylinder (characteristic (pointCode ⁻¹' s)) = characteristic (cylinder s) := by
  classical
  ext p
  change (if pointCode (pointCode.symm p.1) ∈ s then (1 : ℝ) else 0) =
    if p.1 ∈ s then 1 else 0
  simp

theorem compressCylinder_mem {I : Type*} (J : I → Set ℕ)
    {f : Ambient} (hf : f ∈ CylinderJL (cylinderFamily J)) :
    compressCylinder f ∈ JL (cylinderBaseFamily J) := by
  have hle : CylinderJL (cylinderFamily J) ≤
      (JL (cylinderBaseFamily J)).comap compressCylinder.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro g hg
      change compressCylinder g ∈ JL (cylinderBaseFamily J)
      rcases hg with (⟨n, rfl⟩ | ⟨a, ⟨i, rfl⟩, rfl⟩) | rfl
      · rw [compressCylinder_characteristic]
        have hs : pointCode ⁻¹' ({n} : Set ℕ) = {pointCode.symm n} := by
          ext p
          exact pointCode.apply_eq_iff_eq_symm_apply
        rw [hs]
        exact characteristic_singleton_mem_JL _ _
      · rw [compressCylinder_characteristic]
        exact characteristic_mem_JL ⟨i, rfl⟩
      · have h : compressCylinder (characteristic Set.univ) = characteristic Set.univ := by
          ext p; simp
        rw [h]
        exact constant_mem_JL _
    · exact (Submodule.isClosed_topologicalClosure _).preimage compressCylinder.continuous
  exact hle hf

theorem expandCylinder_mem {I : Type*} (J : I → Set ℕ)
    {f : Ambient} (hf : f ∈ JL (cylinderBaseFamily J)) :
    expandCylinder f ∈ CylinderJL (cylinderFamily J) := by
  have hle : JL (cylinderBaseFamily J) ≤
      (CylinderJL (cylinderFamily J)).comap expandCylinder.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro g hg
      change expandCylinder g ∈ CylinderJL (cylinderFamily J)
      rcases hg with (⟨p, rfl⟩ | ⟨a, ⟨i, rfl⟩, rfl⟩) | rfl
      · have hs : ({p} : Set Point) = pointCode ⁻¹' {pointCode p} := by ext q; simp
        rw [hs, expandCylinder_characteristic]
        exact characteristic_fibre_mem_CylinderJL _ _
      · rw [expandCylinder_characteristic]
        exact characteristic_mem_CylinderJL ⟨i, rfl⟩
      · have h : expandCylinder (characteristic Set.univ) = characteristic Set.univ := by
          ext p; simp
        rw [h]
        exact constant_mem_CylinderJL _
    · exact (Submodule.isClosed_topologicalClosure _).preimage expandCylinder.continuous
  exact hle hf

/-- Relabeling the one-point-per-fibre base gives an isometry of closed spans. -/
def cylinderJLEquiv {I : Type*} (J : I → Set ℕ) :
    CylinderJL (cylinderFamily J) ≃ₗᵢ[ℝ] JL (cylinderBaseFamily J) where
  toFun f := ⟨compressCylinder f, compressCylinder_mem J f.property⟩
  invFun f := ⟨expandCylinder f, expandCylinder_mem J f.property⟩
  left_inv f := Subtype.ext (expand_compressCylinder J f.property)
  right_inv f := Subtype.ext (compress_expandCylinder f)
  map_add' f g := Subtype.ext (map_add compressCylinder f.val g.val)
  map_smul' r f := Subtype.ext (map_smul compressCylinder r f.val)
  norm_map' f := by
    change ‖compressCylinder f.val‖ = ‖f.val‖
    apply le_antisymm (compressCylinder_norm_le _)
    have h := expandCylinder_norm_le (compressCylinder f.val)
    rwa [expand_compressCylinder J f.property] at h

theorem cylinderBaseFamily_almostDisjoint {I : Type*} (J : I → Set ℕ)
    (hinf : ∀ i, (J i).Infinite)
    (hpair : Pairwise (fun i j => (J i ∩ J j).Finite)) :
    AlmostDisjoint (cylinderBaseFamily J) := by
  constructor
  · rintro b ⟨i, rfl⟩
    exact (hinf i).preimage (by simp)
  · rintro b ⟨i, rfl⟩ c ⟨j, rfl⟩ hne
    have hij : i ≠ j := fun h => hne (h ▸ rfl)
    change (pointCode ⁻¹' (J i ∩ J j)).Finite
    exact (hpair hij).preimage pointCode.injective.injOn

theorem cylinderBaseFamily_infinite {I : Type*} [Infinite I] (J : I → Set ℕ)
    (hinf : ∀ i, (J i).Infinite)
    (hpair : Pairwise (fun i j => (J i ∩ J j).Finite)) :
    (cylinderBaseFamily J).Infinite := by
  apply Set.infinite_range_of_injective
  intro i j heq
  have heq' : J i = J j := pointCode.surjective.preimage_injective heq
  by_contra hij
  have hf := hpair hij
  change (J i ∩ J j).Finite at hf
  rw [← heq', Set.inter_self] at hf
  exact hinf i hf

/-- The cylinder copy has its own actual Alexandrov--Urysohn compactum.
The infinite-family hypothesis prevents an extraneous isolated infinity point. -/
def cylinderContinuousEquiv {I : Type*} [Infinite I] (J : I → Set ℕ)
    (hinf : ∀ i, (J i).Infinite)
    (hpair : Pairwise (fun i j => (J i ∩ J j).Finite)) :
    CylinderJL (cylinderFamily J) ≃ₗᵢ[ℝ]
      C(AUCompactum (cylinderBaseFamily J), ℝ) :=
  (cylinderJLEquiv J).trans
    (jlContinuousEquiv (cylinderBaseFamily_almostDisjoint J hinf hpair)
      (cylinderBaseFamily_infinite J hinf hpair))

end SigmaNonprimarity
