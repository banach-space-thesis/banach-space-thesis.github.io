import Posets.FamilyTails
import Posets.FamilySupport
import PosetsCommon.CZeroHomeomorph
import JFA.MrowkaCountableSplit

/-! Continuous linear maps on a Mrówka C₀ space are determined by the
isolated-point indicators and compact-open family indicators. -/

noncomputable section
open scoped ZeroAtInfty
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem map_disjointCzeroSynthesis_eq_zero {ι K : Type*}
    [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace K]
    (η : ι → C₀(K, 𝕜)) (hunit : ∀ i, ‖η i‖ ≤ 1)
    (hd : Pairwise fun i j => Disjoint (Function.support (η i)) (Function.support (η j)))
    (φ : C₀(K, 𝕜) →L[𝕜] F) (hz : ∀ i, φ (η i) = 0) (a : C₀(ι, 𝕜)) :
    φ (JFA.disjointCzeroSynthesis η hunit hd a) = 0 := by
  change φ (∑' i, a i • η i) = 0
  rw [φ.map_tsum (JFA.summable_smul_disjointCzero η hunit hd a)]
  simp only [map_smul, hz, smul_zero, tsum_zero]

theorem map_eq_zero_of_generators (h𝒜 : IsAlmostDisjoint 𝒜)
    (φ : Space 𝕜 𝒜 →L[𝕜] F)
    (hn : ∀ n, φ (isolatedVector 𝕜 𝒜 n) = 0)
    (hA : ∀ A, φ (familyVector 𝕜 𝒜 h𝒜 A) = 0) (f : Space 𝕜 𝒜) : φ f = 0 := by
  classical
  let S := familySupport 𝕜 f
  letI : Countable S := (familySupport_countable f).to_subtype
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  let e : Space 𝕜 𝒜 ≃L[𝕜] C₀(PUnit.{1} × Mrowka 𝒜, 𝕜) :=
    ThesisCommon.cZeroHomeomorphEquiv (Homeomorph.punitProd (Mrowka 𝒜))
  let ψ : C₀(PUnit.{1} × Mrowka 𝒜, 𝕜) →L[𝕜] F := φ.comp e.symm.toContinuousLinearMap
  have hn' (q : PUnit.{1} × ℕ) : ψ (JFA.mrowkaNaturalIndicator h𝒜 q) = 0 := by
    have he : e.symm (JFA.mrowkaNaturalIndicator (𝕜 := 𝕜) h𝒜 q) =
        isolatedVector 𝕜 𝒜 q.2 := by
      apply e.injective
      rw [e.apply_symm_apply]
      ext p
      rcases p with ⟨d, p⟩
      cases p with
      | inl n =>
        change JFA.mrowkaNaturalIndicator h𝒜 q (d, Sum.inl n) = isolatedVector 𝕜 𝒜 q.2 (Sum.inl n)
        rw [isolatedVector_natural]
        simp [JFA.mrowkaNaturalIndicator, JLMS.clopenIndicator_apply, JFA.Mrowka]
      | inr A =>
        change JFA.mrowkaNaturalIndicator h𝒜 q (d, Sum.inr A) = isolatedVector 𝕜 𝒜 q.2 (Sum.inr A)
        simp [JFA.mrowkaNaturalIndicator, JLMS.clopenIndicator_apply, isolatedVector_family]
    change φ (e.symm _) = 0
    rw [he, hn]
  have hA' (q : PUnit.{1} × S) : ψ (JFA.mrowkaFamilyIndicator S h𝒜 q) = 0 := by
    have he : e.symm (JFA.mrowkaFamilyIndicator (𝕜 := 𝕜) S h𝒜 q) =
        familyTailVector h𝒜 q.2.val (JFA.mrowkaSelectedTail S h𝒜 q.2) := by
      apply e.injective
      rw [e.apply_symm_apply]
      ext p
      rcases p with ⟨d, p⟩
      change JFA.mrowkaFamilyIndicator S h𝒜 q (d, p) = familyTailVector h𝒜 q.2.val _ p
      simp [JFA.mrowkaFamilyIndicator, familyTailVector, JLMS.clopenIndicator_apply]
    change φ (e.symm _) = 0
    rw [he, functional_familyTailVector h𝒜 φ hn, hA]
  have hf : e f ∈ JFA.mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := PUnit.{1}) S := by
    intro d A hnot
    change f (Sum.inr A) = 0
    by_contra hne
    exact hnot hne
  let x := JFA.mrowkaSupportSplit S h𝒜 ⟨e f, hf⟩
  have hsplit : JFA.mrowkaNaturalLift h𝒜 x.1 + JFA.mrowkaFamilyLift S h𝒜 x.2 = e f :=
    congrArg (fun T => T ⟨e f, hf⟩) (JFA.mrowkaSupportJoin_split (𝕜 := 𝕜) (D := PUnit.{1}) S h𝒜)
  have hfirst : ψ (JFA.mrowkaNaturalLift h𝒜 x.1) = 0 :=
    map_disjointCzeroSynthesis_eq_zero _ _ _ ψ hn' x.1
  have hsecond : ψ (JFA.mrowkaFamilyLift S h𝒜 x.2) = 0 :=
    map_disjointCzeroSynthesis_eq_zero _ _ _ ψ hA' x.2
  have heq := congrArg ψ hsplit
  rw [map_add, hfirst, hsecond, zero_add] at heq
  have hback : ψ (e f) = φ f := by
    change φ (e.symm (e f)) = φ f
    rw [e.symm_apply_apply]
  exact hback.symm.trans heq.symm

theorem continuousLinearMap_ext_generators (h𝒜 : IsAlmostDisjoint 𝒜)
    (φ ψ : Space 𝕜 𝒜 →L[𝕜] F)
    (hn : ∀ n, φ (isolatedVector 𝕜 𝒜 n) = ψ (isolatedVector 𝕜 𝒜 n))
    (hA : ∀ A, φ (familyVector 𝕜 𝒜 h𝒜 A) = ψ (familyVector 𝕜 𝒜 h𝒜 A)) : φ = ψ := by
  ext f
  exact sub_eq_zero.mp (map_eq_zero_of_generators h𝒜 (φ - ψ)
    (fun n => sub_eq_zero.mpr (hn n)) (fun A => sub_eq_zero.mpr (hA A)) f)

end Posets
