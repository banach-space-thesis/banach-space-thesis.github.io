import Sigma.ComplexContinuousRepresentation
import Sigma.CylinderRepresentation

/-! The fibre-constant cylinder space is a genuine C(K) space. We relabel its
countable base by `pointCode`, keeping one base point for each whole fibre. -/
noncomputable section
open Set
namespace SigmaNonprimarity

def complexCompressCylinder : ComplexAmbient →L[ℂ] ComplexAmbient :=
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

def complexExpandCylinder : ComplexAmbient →L[ℂ] ComplexAmbient :=
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

@[simp] theorem complexCompressCylinder_apply (f : ComplexAmbient) (p : Point) :
    complexCompressCylinder f p = f (pointCode p, false) := rfl

@[simp] theorem complexExpandCylinder_apply (f : ComplexAmbient) (p : Point) :
    complexExpandCylinder f p = f (pointCode.symm p.1) := rfl

theorem complexCompressCylinder_norm_le (f : ComplexAmbient) : ‖complexCompressCylinder f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    (fun _ => f.norm_coe_le_norm _)

theorem complexExpandCylinder_norm_le (f : ComplexAmbient) : ‖complexExpandCylinder f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    (fun _ => f.norm_coe_le_norm _)

theorem compress_complexExpandCylinder (f : ComplexAmbient) : complexCompressCylinder (complexExpandCylinder f) = f := by
  ext p
  simp

theorem expand_complexCompressCylinder {I : Type*} (J : I → Set ℕ)
    {f : ComplexAmbient} (hf : f ∈ ComplexCylinderJL (cylinderFamily J)) :
    complexExpandCylinder (complexCompressCylinder f) = f := by
  have h := (complexAverage_eq_self_iff f).mp (complexAverage_eq_self_of_mem_complexCylinderJL J hf)
  ext ⟨n, b⟩
  cases b <;> simp [h]

theorem complexCompressCylinder_characteristic (s : Set ℕ) :
    complexCompressCylinder (complexCharacteristic (cylinder s)) = complexCharacteristic (pointCode ⁻¹' s) := by
  ext p
  rfl

theorem complexExpandCylinder_characteristic (s : Set ℕ) :
    complexExpandCylinder (complexCharacteristic (pointCode ⁻¹' s)) = complexCharacteristic (cylinder s) := by
  classical
  ext p
  change (if pointCode (pointCode.symm p.1) ∈ s then (1 : ℂ) else 0) =
    if p.1 ∈ s then 1 else 0
  simp

theorem complexCompressCylinder_mem {I : Type*} (J : I → Set ℕ)
    {f : ComplexAmbient} (hf : f ∈ ComplexCylinderJL (cylinderFamily J)) :
    complexCompressCylinder f ∈ ComplexJL (cylinderBaseFamily J) := by
  have hle : ComplexCylinderJL (cylinderFamily J) ≤
      (ComplexJL (cylinderBaseFamily J)).comap complexCompressCylinder.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro g hg
      change complexCompressCylinder g ∈ ComplexJL (cylinderBaseFamily J)
      rcases hg with (⟨n, rfl⟩ | ⟨a, ⟨i, rfl⟩, rfl⟩) | rfl
      · rw [complexCompressCylinder_characteristic]
        have hs : pointCode ⁻¹' ({n} : Set ℕ) = {pointCode.symm n} := by
          ext p
          exact pointCode.apply_eq_iff_eq_symm_apply
        rw [hs]
        exact complexCharacteristic_singleton_mem_ComplexJL _ _
      · rw [complexCompressCylinder_characteristic]
        exact complexCharacteristic_mem_ComplexJL ⟨i, rfl⟩
      · have h : complexCompressCylinder (complexCharacteristic Set.univ) = complexCharacteristic Set.univ := by
          ext p; simp
        rw [h]
        exact complexConstant_mem_ComplexJL _
    · exact (Submodule.isClosed_topologicalClosure _).preimage complexCompressCylinder.continuous
  exact hle hf

theorem complexExpandCylinder_mem {I : Type*} (J : I → Set ℕ)
    {f : ComplexAmbient} (hf : f ∈ ComplexJL (cylinderBaseFamily J)) :
    complexExpandCylinder f ∈ ComplexCylinderJL (cylinderFamily J) := by
  have hle : ComplexJL (cylinderBaseFamily J) ≤
      (ComplexCylinderJL (cylinderFamily J)).comap complexExpandCylinder.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro g hg
      change complexExpandCylinder g ∈ ComplexCylinderJL (cylinderFamily J)
      rcases hg with (⟨p, rfl⟩ | ⟨a, ⟨i, rfl⟩, rfl⟩) | rfl
      · have hs : ({p} : Set Point) = pointCode ⁻¹' {pointCode p} := by ext q; simp
        rw [hs, complexExpandCylinder_characteristic]
        exact complexCharacteristic_fibre_mem_ComplexCylinderJL _ _
      · rw [complexExpandCylinder_characteristic]
        exact complexCharacteristic_mem_ComplexCylinderJL ⟨i, rfl⟩
      · have h : complexExpandCylinder (complexCharacteristic Set.univ) = complexCharacteristic Set.univ := by
          ext p; simp
        rw [h]
        exact complexConstant_mem_ComplexCylinderJL _
    · exact (Submodule.isClosed_topologicalClosure _).preimage complexExpandCylinder.continuous
  exact hle hf

/-- Relabeling the one-point-per-fibre base gives an isometry of closed spans. -/
def complexCylinderJLEquiv {I : Type*} (J : I → Set ℕ) :
    ComplexCylinderJL (cylinderFamily J) ≃ₗᵢ[ℂ] ComplexJL (cylinderBaseFamily J) where
  toFun f := ⟨complexCompressCylinder f, complexCompressCylinder_mem J f.property⟩
  invFun f := ⟨complexExpandCylinder f, complexExpandCylinder_mem J f.property⟩
  left_inv f := Subtype.ext (expand_complexCompressCylinder J f.property)
  right_inv f := Subtype.ext (compress_complexExpandCylinder f)
  map_add' f g := Subtype.ext (map_add complexCompressCylinder f.val g.val)
  map_smul' r f := Subtype.ext (map_smul complexCompressCylinder r f.val)
  norm_map' f := by
    change ‖complexCompressCylinder f.val‖ = ‖f.val‖
    apply le_antisymm (complexCompressCylinder_norm_le _)
    have h := complexExpandCylinder_norm_le (complexCompressCylinder f.val)
    rwa [expand_complexCompressCylinder J f.property] at h

/-- The cylinder copy has its own actual Alexandrov--Urysohn compactum.
The infinite-family hypothesis prevents an extraneous isolated infinity point. -/
def complexCylinderContinuousEquiv {I : Type*} [Infinite I] (J : I → Set ℕ)
    (hinf : ∀ i, (J i).Infinite)
    (hpair : Pairwise (fun i j => (J i ∩ J j).Finite)) :
    ComplexCylinderJL (cylinderFamily J) ≃ₗᵢ[ℂ]
      C(AUCompactum (cylinderBaseFamily J), ℂ) :=
  (complexCylinderJLEquiv J).trans
    (complexJLContinuousEquiv (cylinderBaseFamily_almostDisjoint J hinf hpair)
      (cylinderBaseFamily_infinite J hinf hpair))

end SigmaNonprimarity


