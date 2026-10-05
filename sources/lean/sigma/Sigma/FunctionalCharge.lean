import Sigma.AtomCharges

/-! Extend each actual unit JL functional to a finite-variation charge on the
full power set. Agreement includes singleton indicators, family indicators,
and the constant function, so the infinity atom is retained. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity

local instance bridgeRealSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace
local instance bridgeJLGroup (B : Set (Set Point)) : NormedAddCommGroup (JL B) := inferInstance
local instance bridgeJLSpace (B : Set (Set Point)) : NormedSpace ℝ (JL B) := inferInstance

theorem jlDual_apply_hasSum {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (φ : JL B →L[ℝ] ℝ) (f : JL B) :
    HasSum (fun p => jlDualEquiv hB hInf φ p * jlContinuousEquiv hB hInf f p) (φ f) := by
  let e := (jlContinuousEquiv hB hInf).trans (compactCZeroEquiv (AUCompactum B))
  have h := JLMS.atomicDual_apply_hasSum (Classical.choice (auAtomicDualModel hB))
    (dualIsometryEquiv e φ) (e f)
  simpa only [dualIsometryEquiv_apply, LinearIsometryEquiv.symm_apply_apply] using h

def functionalCharge {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (Uinf : Ultrafilter Point) (φ : JL B →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) : UnitCharge Point :=
  lpChargeSeries (jlDualEquiv hB hInf φ) (by simpa using hφ) (atomCharge hB Uinf)

theorem functionalCharge_apply {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (Uinf : Ultrafilter Point) (φ : JL B →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) (A : Set Point) :
    functionalCharge hB hInf Uinf φ hφ A = ∑' p, jlDualEquiv hB hInf φ p * atomCharge hB Uinf p A := rfl

theorem functionalCharge_eq_of_lift {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (Uinf : Ultrafilter Point) (φ : JL B →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    (A : Set Point) (hA : characteristic A ∈ JL B) (f : C(AUCompactum B, ℝ))
    (hf : restrictToBase B f = characteristic A)
    (hatom : ∀ p, atomCharge hB Uinf p A = f p) :
    functionalCharge hB hInf Uinf φ hφ A = φ ⟨characteristic A,hA⟩ := by
  have h := jlDual_apply_hasSum hB hInf φ ⟨characteristic A,hA⟩
  have heq : jlContinuousEquiv hB hInf ⟨characteristic A,hA⟩ = f := by
    simpa only [hf] using jlContinuousEquiv_restrict hB hInf f (hf ▸ hA)
  rw [heq] at h
  rw [functionalCharge_apply]
  simpa only [hatom] using h.tsum_eq

theorem functionalCharge_singleton {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (Uinf : Ultrafilter Point) (hUinf : (Uinf : Filter Point) ≤ Filter.cofinite)
    (φ : JL B →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) (n : Point) :
    functionalCharge hB hInf Uinf φ hφ {n} = φ ⟨characteristic {n}, characteristic_singleton_mem_JL B n⟩ :=
  functionalCharge_eq_of_lift hB hInf Uinf φ hφ {n} _ (singletonFunction hB n)
    (restrict_singletonFunction hB n) (atomCharge_singleton hB Uinf hUinf n)

theorem functionalCharge_family {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (Uinf : Ultrafilter Point) (havoid : ∀ b ∈ B, b ∉ Uinf)
    (φ : JL B →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) (b : B) :
    functionalCharge hB hInf Uinf φ hφ b.val = φ ⟨characteristic b.val, characteristic_mem_JL b.property⟩ :=
  functionalCharge_eq_of_lift hB hInf Uinf φ hφ b.val _ (tailFunction hB b)
    (restrict_tailFunction hB b) (atomCharge_family_set hB Uinf havoid b)

theorem functionalCharge_one {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (Uinf : Ultrafilter Point) (φ : JL B →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) :
    functionalCharge hB hInf Uinf φ hφ Set.univ = φ ⟨characteristic Set.univ, constant_mem_JL B⟩ := by
  apply functionalCharge_eq_of_lift hB hInf Uinf φ hφ Set.univ _ 1
  · simpa only [map_one] using (characteristic_univ).symm
  · exact fun p => atomCharge_univ hB Uinf p

end SigmaNonprimarity
