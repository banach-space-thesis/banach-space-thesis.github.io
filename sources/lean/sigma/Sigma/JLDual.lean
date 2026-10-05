import Sigma.AtomicRepresentation
import Sigma.ContinuousRepresentation
import ThesisCommon.Analysis.IsometricDual

noncomputable section
open scoped ZeroAtInfty
namespace SigmaNonprimarity

local instance realSelfNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace
local instance jlGroup (B : Set (Set Point)) : NormedAddCommGroup (JL B) := inferInstance
local instance jlSpace (B : Set (Set Point)) : NormedSpace ℝ (JL B) := inferInstance

local instance jlDualGroup (B : Set (Set Point)) : NormedAddCommGroup (JL B →L[ℝ] ℝ) :=
  inferInstance
local instance jlDualSpace (B : Set (Set Point)) : NormedSpace ℝ (JL B →L[ℝ] ℝ) :=
  inferInstance

/-- On a compact domain, vanishing at infinity imposes no further condition. -/
def compactCZeroEquiv (K : Type*) [TopologicalSpace K] [CompactSpace K] :
    C(K, ℝ) ≃ₗᵢ[ℝ] C₀(K, ℝ) where
  toEquiv := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
  map_add' := by intros; ext p; rfl
  map_smul' := by intros; ext p; rfl
  norm_map' := by intro f; rfl

/-- The actual isometric atomic representation of JL(B)*, with all K_B coordinates. -/
def jlDualEquiv {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite) :
    (JL B →L[ℝ] ℝ) ≃ₗᵢ[ℝ] JLMS.ellOneOn ℝ (AUCompactum B) :=
  (ThesisCommon.dualIsometryEquiv
    ((jlContinuousEquiv hB hInf).trans (compactCZeroEquiv (AUCompactum B)))).trans
      (Classical.choice (auAtomicDualModel hB)).representation

/-- The infinity atom is a bounded functional on the actual JL space. -/
def infinityFunctional {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite) :
    JL B →L[ℝ] ℝ :=
  (JLMS.evaluation (𝕜 := ℝ) (OnePoint.infty : AUCompactum B)).comp
    (((jlContinuousEquiv hB hInf).trans
      (compactCZeroEquiv (AUCompactum B))).toContinuousLinearEquiv.toContinuousLinearMap)

theorem infinityFunctional_restrict {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (hInf : B.Infinite) (f : C(AUCompactum B, ℝ)) (hf : restrictToBase B f ∈ JL B) :
    infinityFunctional hB hInf ⟨restrictToBase B f, hf⟩ = f OnePoint.infty := by
  change (jlContinuousEquiv hB hInf ⟨restrictToBase B f, hf⟩) OnePoint.infty = _
  rw [jlContinuousEquiv_restrict]

@[simp] theorem infinityFunctional_singleton {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (hInf : B.Infinite) (p : Point) :
    infinityFunctional hB hInf ⟨characteristic {p}, characteristic_singleton_mem_JL B p⟩ = 0 := by
  have h := infinityFunctional_restrict hB hInf (singletonFunction hB p)
    (restrictToBase_mem_JL hB _)
  simpa only [restrict_singletonFunction, singletonFunction_apply, OnePoint.infty_ne_coe,
    ↓reduceIte] using h

@[simp] theorem infinityFunctional_family {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (hInf : B.Infinite) (b : B) :
    infinityFunctional hB hInf ⟨characteristic b.val, characteristic_mem_JL b.property⟩ = 0 := by
  have h := infinityFunctional_restrict hB hInf (tailFunction hB b)
    (restrictToBase_mem_JL hB _)
  simpa only [restrict_tailFunction, tailFunction_infty] using h

@[simp] theorem infinityFunctional_one {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (hInf : B.Infinite) :
    infinityFunctional hB hInf ⟨characteristic Set.univ, constant_mem_JL B⟩ = 1 := by
  have h := infinityFunctional_restrict hB hInf 1 (restrictToBase_mem_JL hB _)
  simpa only [map_one, characteristic_univ, ContinuousMap.one_apply] using h

/-- The two families of coordinates printed in Section 3.2 do not determine a functional.
They omit an independent coordinate, namely its value on the constant function. -/
theorem printed_dual_coordinates_not_injective {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) :
    ∃ φ : JL B →L[ℝ] ℝ, φ ≠ 0 ∧
      (∀ p : Point, φ ⟨characteristic {p}, characteristic_singleton_mem_JL B p⟩ = 0) ∧
      (∀ b : B, φ ⟨characteristic b.val, characteristic_mem_JL b.property⟩ = 0) := by
  refine ⟨infinityFunctional hB hInf, ?_, infinityFunctional_singleton hB hInf,
    infinityFunctional_family hB hInf⟩
  intro hzero
  have h := infinityFunctional_one hB hInf
  rw [hzero] at h
  norm_num at h

end SigmaNonprimarity
