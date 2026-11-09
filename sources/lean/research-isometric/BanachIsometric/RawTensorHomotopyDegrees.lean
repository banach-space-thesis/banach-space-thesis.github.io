import BanachIsometric.RawTensorHomotopyMaps
import BanachIsometric.RawTensorAugmentation

/-! The actual tensor homotopy raises total degree by one. On contractible
factors its homology projector vanishes in positive total degree, and in
degree zero on the kernel of the literal product augmentation. -/

noncomputable section
namespace BanachIsometric.SingularAW
open SingularPrism
open scoped TensorProduct DirectSum

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

theorem rawTensorBothProjector_inclusion (p q : ℕ) (c : RawTensorChains X Y p q) :
    rawTensorBothProjector X Y (rawTensorInclusion X Y p q c) =
      rawTensorInclusion X Y p q
        (TensorProduct.map (rawFactorProjector X p) (rawFactorProjector Y q) c) := by
  simp only [rawTensorBothProjector, rawTensorInclusion, DirectSum.toModule_lof, LinearMap.comp_apply]

theorem rawTensorLeftHomotopy_inclusion (p q : ℕ) (c : RawTensorChains X Y p q) :
    rawTensorLeftHomotopy X Y (rawTensorInclusion X Y p q c) =
      rawTensorInclusion X Y (p + 1) q
        (TensorProduct.map (rawFactorContraction X p) LinearMap.id c) := by
  simp only [rawTensorLeftHomotopy, rawTensorInclusion, DirectSum.toModule_lof, LinearMap.comp_apply]

theorem rawTensorRightHomotopy_inclusion (p q : ℕ) (c : RawTensorChains X Y p q) :
    rawTensorRightHomotopy X Y (rawTensorInclusion X Y p q c) =
      (-1 : ℚ) ^ p • rawTensorInclusion X Y p (q + 1)
        (TensorProduct.map (rawFactorProjector X p) (rawFactorContraction Y q) c) := by
  simp only [rawTensorRightHomotopy, rawTensorInclusion, DirectSum.toModule_lof,
    LinearMap.comp_apply, LinearMap.smul_apply]

theorem rawTensorComponent_bothProjector (p q : ℕ) (c : RawBigradedTensorChains X Y) :
    rawTensorComponent X Y p q (rawTensorBothProjector X Y c) =
      TensorProduct.map (rawFactorProjector X p) (rawFactorProjector Y q)
        (rawTensorComponent X Y p q c) := by
  have h : (rawTensorComponent X Y p q).comp (rawTensorBothProjector X Y) =
      (TensorProduct.map (rawFactorProjector X p) (rawFactorProjector Y q)).comp
        (rawTensorComponent X Y p q) := by
    apply DirectSum.linearMap_ext
    rintro ⟨r, s⟩
    apply LinearMap.ext
    intro z
    change rawTensorComponent X Y p q (rawTensorBothProjector X Y (rawTensorInclusion X Y r s z)) =
      TensorProduct.map (rawFactorProjector X p) (rawFactorProjector Y q)
        (rawTensorComponent X Y p q (rawTensorInclusion X Y r s z))
    rw [rawTensorBothProjector_inclusion]
    by_cases he : (r, s) = (p, q)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [rawTensorComponent_inclusion, rawTensorComponent_inclusion]
    · rw [rawTensorComponent_inclusion_of_ne X Y he, rawTensorComponent_inclusion_of_ne X Y he, map_zero]
  exact LinearMap.congr_fun h c

theorem rawTensorComponent_leftHomotopy_zero (q : ℕ) (c : RawBigradedTensorChains X Y) :
    rawTensorComponent X Y 0 q (rawTensorLeftHomotopy X Y c) = 0 := by
  have h : (rawTensorComponent X Y 0 q).comp (rawTensorLeftHomotopy X Y) = 0 := by
    apply DirectSum.linearMap_ext
    rintro ⟨r, s⟩
    apply LinearMap.ext
    intro z
    change rawTensorComponent X Y 0 q (rawTensorLeftHomotopy X Y (rawTensorInclusion X Y r s z)) = 0
    rw [rawTensorLeftHomotopy_inclusion]
    apply rawTensorComponent_inclusion_of_ne X Y
    intro he
    have hfst := congrArg Prod.fst he
    change r + 1 = 0 at hfst
    omega
  exact LinearMap.congr_fun h c

theorem rawTensorComponent_leftHomotopy_succ (p q : ℕ) (c : RawBigradedTensorChains X Y) :
    rawTensorComponent X Y (p + 1) q (rawTensorLeftHomotopy X Y c) =
      TensorProduct.map (rawFactorContraction X p) LinearMap.id (rawTensorComponent X Y p q c) := by
  have h : (rawTensorComponent X Y (p + 1) q).comp (rawTensorLeftHomotopy X Y) =
      (TensorProduct.map (rawFactorContraction X p) LinearMap.id).comp (rawTensorComponent X Y p q) := by
    apply DirectSum.linearMap_ext
    rintro ⟨r, s⟩
    apply LinearMap.ext
    intro z
    change rawTensorComponent X Y (p + 1) q
      (rawTensorLeftHomotopy X Y (rawTensorInclusion X Y r s z)) =
      TensorProduct.map (rawFactorContraction X p) LinearMap.id
        (rawTensorComponent X Y p q (rawTensorInclusion X Y r s z))
    rw [rawTensorLeftHomotopy_inclusion]
    by_cases he : (r, s) = (p, q)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [rawTensorComponent_inclusion, rawTensorComponent_inclusion]
    · have he' : (r + 1, s) ≠ (p + 1, q) := by
        intro hpair
        apply he
        apply Prod.ext
        · have hfst := congrArg Prod.fst hpair
          change r + 1 = p + 1 at hfst
          omega
        · have hsnd := congrArg Prod.snd hpair
          exact hsnd
      rw [rawTensorComponent_inclusion_of_ne X Y he', rawTensorComponent_inclusion_of_ne X Y he, map_zero]
  exact LinearMap.congr_fun h c

theorem rawTensorComponent_rightHomotopy_zero (p : ℕ) (c : RawBigradedTensorChains X Y) :
    rawTensorComponent X Y p 0 (rawTensorRightHomotopy X Y c) = 0 := by
  have h : (rawTensorComponent X Y p 0).comp (rawTensorRightHomotopy X Y) = 0 := by
    apply DirectSum.linearMap_ext
    rintro ⟨r, s⟩
    apply LinearMap.ext
    intro z
    change rawTensorComponent X Y p 0 (rawTensorRightHomotopy X Y (rawTensorInclusion X Y r s z)) = 0
    rw [rawTensorRightHomotopy_inclusion, map_smul]
    have he : (r, s + 1) ≠ (p, 0) := by
      intro hpair
      have hsnd := congrArg Prod.snd hpair
      change s + 1 = 0 at hsnd
      omega
    rw [rawTensorComponent_inclusion_of_ne X Y he, smul_zero]
  exact LinearMap.congr_fun h c

theorem rawTensorComponent_rightHomotopy_succ (p q : ℕ) (c : RawBigradedTensorChains X Y) :
    rawTensorComponent X Y p (q + 1) (rawTensorRightHomotopy X Y c) =
      (-1 : ℚ) ^ p • TensorProduct.map (rawFactorProjector X p) (rawFactorContraction Y q)
        (rawTensorComponent X Y p q c) := by
  have h : (rawTensorComponent X Y p (q + 1)).comp (rawTensorRightHomotopy X Y) =
      ((-1 : ℚ) ^ p • TensorProduct.map (rawFactorProjector X p) (rawFactorContraction Y q)).comp
        (rawTensorComponent X Y p q) := by
    apply DirectSum.linearMap_ext
    rintro ⟨r, s⟩
    apply LinearMap.ext
    intro z
    change rawTensorComponent X Y p (q + 1)
      (rawTensorRightHomotopy X Y (rawTensorInclusion X Y r s z)) =
      (-1 : ℚ) ^ p • TensorProduct.map (rawFactorProjector X p) (rawFactorContraction Y q)
        (rawTensorComponent X Y p q (rawTensorInclusion X Y r s z))
    rw [rawTensorRightHomotopy_inclusion, map_smul]
    by_cases he : (r, s) = (p, q)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [rawTensorComponent_inclusion, rawTensorComponent_inclusion]
    · have he' : (r, s + 1) ≠ (p, q + 1) := by
        intro hpair
        apply he
        apply Prod.ext
        · have hfst := congrArg Prod.fst hpair
          exact hfst
        · have hsnd := congrArg Prod.snd hpair
          change s + 1 = q + 1 at hsnd
          omega
      rw [rawTensorComponent_inclusion_of_ne X Y he', rawTensorComponent_inclusion_of_ne X Y he,
        map_zero, smul_zero, smul_zero]
  exact LinearMap.congr_fun h c

theorem rawTensorTotalHomotopy_mem_totalDegree (n : ℕ) {c : RawBigradedTensorChains X Y}
    (hc : c ∈ rawTensorTotalDegree X Y n) :
    rawTensorTotalHomotopy X Y c ∈ rawTensorTotalDegree X Y (n + 1) := by
  have hL : rawTensorLeftHomotopy X Y c ∈ rawTensorTotalDegree X Y (n + 1) := by
    intro p q hpq
    cases p with
    | zero => exact rawTensorComponent_leftHomotopy_zero X Y q c
    | succ p => rw [rawTensorComponent_leftHomotopy_succ, hc p q (by omega), map_zero]
  have hR : rawTensorRightHomotopy X Y c ∈ rawTensorTotalDegree X Y (n + 1) := by
    intro p q hpq
    cases q with
    | zero => exact rawTensorComponent_rightHomotopy_zero X Y p c
    | succ q => rw [rawTensorComponent_rightHomotopy_succ, hc p q (by omega), map_zero, smul_zero]
  exact (rawTensorTotalDegree X Y (n + 1)).add_mem hL hR

theorem rawTensorBothProjector_eq_zero_of_positive_totalDegree
    [ContractibleSpace X] [ContractibleSpace Y] (n : ℕ) {c : RawBigradedTensorChains X Y}
    (hc : c ∈ rawTensorTotalDegree X Y (n + 1)) : rawTensorBothProjector X Y c = 0 := by
  apply DirectSum.ext_component ℚ
  rintro ⟨p, q⟩
  change rawTensorComponent X Y p q (rawTensorBothProjector X Y c) = 0
  rw [rawTensorComponent_bothProjector]
  cases p with
  | zero =>
      cases q with
      | zero => rw [hc 0 0 (by omega), map_zero]
      | succ q => rw [rawFactorProjector_succ_eq_zero Y q, TensorProduct.map_zero_right, LinearMap.zero_apply]
  | succ p => rw [rawFactorProjector_succ_eq_zero X p, TensorProduct.map_zero_left, LinearMap.zero_apply]

theorem rawTensorBothProjector_eq_zero_of_zero_totalDegree_augmentation
    [ContractibleSpace X] [ContractibleSpace Y] {c : RawBigradedTensorChains X Y}
    (hc : c ∈ rawTensorTotalDegree X Y 0) (ha : rawTensorAugmentation X Y c = 0) :
    rawTensorBothProjector X Y c = 0 := by
  apply DirectSum.ext_component ℚ
  rintro ⟨p, q⟩
  change rawTensorComponent X Y p q (rawTensorBothProjector X Y c) = 0
  rw [rawTensorComponent_bothProjector]
  by_cases hpq : p + q = 0
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p
    subst q
    exact rawTensorZeroProjector_eq_zero_of_augmentation X Y ha
  · rw [hc p q hpq, map_zero]

end BanachIsometric.SingularAW
