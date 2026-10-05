import Sigma.PairedCoefficients
import Sigma.GeneratedCharge
import Sigma.HistoryCharges

/-! Actual product-dual functionals give paired unit-variation charges, with
agreement on the full product of the two generated Boolean algebras. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace
attribute [local instance] pairedJLGroup pairedJLSpace pairedJLDualGroup

def pairedBaseSet (A D : Set Point) : Set (ℕ ⊕ ℕ) :=
  (Sum.inl '' codedSet A) ∪ (Sum.inr '' codedSet D)

theorem putInCopy_false_pairedBaseSet (μ : UnitCharge Point) (A D : Set Point) :
    putInCopy false μ (pairedBaseSet A D) = μ A := by
  unfold putInCopy
  rw [UnitCharge.map_apply]
  congr 1
  ext p
  simp [pairedBaseSet,codedSet]

theorem putInCopy_true_pairedBaseSet (μ : UnitCharge Point) (A D : Set Point) :
    putInCopy true μ (pairedBaseSet A D) = μ D := by
  unfold putInCopy
  rw [UnitCharge.map_apply]
  congr 1
  ext p
  simp [pairedBaseSet,codedSet]

def pairedAtomCharge {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (e : Λ ≃ B) (et : Λ ≃ Bt)
    (Uinf : Ultrafilter Point) (p : Bool × IndexedAtom Λ) : PairedMeasure :=
  if p.1 then putInCopy true (atomCharge hBt Uinf (compactumAtomEquiv et p.2))
  else putInCopy false (atomCharge hB Uinf (compactumAtomEquiv e p.2))

def pairedFunctionalCharge {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (Uinf : Ultrafilter Point)
    (φ : (JL B × JL Bt) →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) : PairedMeasure :=
  lpChargeSeries (pairedJLCoefficients hB hBt hInf htInf e et φ)
    (by simpa using hφ) (pairedAtomCharge hB hBt e et Uinf)

theorem pairedFunctionalCharge_eq_of_lifts {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (Uinf : Ultrafilter Point)
    (φ : (JL B × JL Bt) →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    (A D : Set Point) (f : C(AUCompactum B,ℝ)) (g : C(AUCompactum Bt,ℝ))
    (hf : ∀ p, atomCharge hB Uinf p A = f p) (hg : ∀ p, atomCharge hBt Uinf p D = g p) :
    pairedFunctionalCharge hB hBt hInf htInf e et Uinf φ hφ (pairedBaseSet A D) =
      φ (⟨restrictToBase B f,restrictToBase_mem_JL hB f⟩,
         ⟨restrictToBase Bt g,restrictToBase_mem_JL hBt g⟩) := by
  let fJL : JL B := ⟨restrictToBase B f,restrictToBase_mem_JL hB f⟩
  let gJL : JL Bt := ⟨restrictToBase Bt g,restrictToBase_mem_JL hBt g⟩
  have hs := pairedJLCoefficients_apply_hasSum hB hBt hInf htInf e et φ fJL gJL
  change (∑' p, pairedJLCoefficients hB hBt hInf htInf e et φ p *
    pairedAtomCharge hB hBt e et Uinf p (pairedBaseSet A D)) = _
  rw [← hs.tsum_eq]
  apply tsum_congr
  rintro ⟨side,p⟩
  congr 1
  cases side
  · change putInCopy false (atomCharge hB Uinf (compactumAtomEquiv e p)) (pairedBaseSet A D) = _
    rw [putInCopy_false_pairedBaseSet,hf]
    exact (congrArg (fun u : C(AUCompactum B,ℝ) => u (compactumAtomEquiv e p))
      (jlContinuousEquiv_restrict hB hInf f (restrictToBase_mem_JL hB f))).symm
  · change putInCopy true (atomCharge hBt Uinf (compactumAtomEquiv et p)) (pairedBaseSet A D) = _
    rw [putInCopy_true_pairedBaseSet,hg]
    exact (congrArg (fun u : C(AUCompactum Bt,ℝ) => u (compactumAtomEquiv et p))
      (jlContinuousEquiv_restrict hBt htInf g (restrictToBase_mem_JL hBt g))).symm

theorem pairedFunctionalCharge_generated {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (Uinf : Ultrafilter Point)
    (hfree : (Uinf : Filter Point) ≤ Filter.cofinite)
    (havoid : ∀ b ∈ B, b ∉ Uinf) (havoidt : ∀ b ∈ Bt, b ∉ Uinf)
    (φ : (JL B × JL Bt) →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    {A D : Set Point} (hA : A ∈ generatedAlgebra B) (hD : D ∈ generatedAlgebra Bt) :
    ∃ (hmemA : characteristic A ∈ JL B) (hmemD : characteristic D ∈ JL Bt),
      pairedFunctionalCharge hB hBt hInf htInf e et Uinf φ hφ (pairedBaseSet A D) =
        φ (⟨characteristic A,hmemA⟩,⟨characteristic D,hmemD⟩) := by
  obtain ⟨f,hf⟩ := atomLiftable_generated hB Uinf hfree havoid hA
  obtain ⟨g,hg⟩ := atomLiftable_generated hBt Uinf hfree havoidt hD
  have hrf := atomLift_restrict hB Uinf hf
  have hrg := atomLift_restrict hBt Uinf hg
  refine ⟨hrf ▸ restrictToBase_mem_JL hB f,hrg ▸ restrictToBase_mem_JL hBt g,?_⟩
  simpa only [hrf,hrg] using pairedFunctionalCharge_eq_of_lifts hB hBt hInf htInf e et Uinf φ hφ A D f g hf hg

end SigmaNonprimarity
