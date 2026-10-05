import Posets.AlspachCounterexampleProbabilityEvaluation
import Posets.WolfeMass

/-! The mass of a finite positive probability tree is exactly the variation
mass of its actual real or complex atomic functional. This gives direct
access to Wolfe's mass inequalities for the constructed rows. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
namespace AlspachProbability
variable {𝕜 K L : Type*} [RCLike 𝕜]

def mass : AlspachProbability K → Set K → ℝ
  | .point k, U => if k ∈ U then 1 else 0
  | .average p q, U => (1 / 2 : ℝ) * (p.mass U + q.mass U)

theorem mass_nonneg (p : AlspachProbability K) (U : Set K) : 0 ≤ p.mass U := by
  induction p with
  | point k => simp only [mass]; split <;> norm_num
  | average p q hp hq => exact mul_nonneg (by norm_num) (add_nonneg hp hq)

theorem mass_le_one (p : AlspachProbability K) (U : Set K) : p.mass U ≤ 1 := by
  induction p with
  | point k => simp only [mass]; split <;> norm_num
  | average p q hp hq => simp only [mass]; linarith

@[simp] theorem mass_univ (p : AlspachProbability K) : p.mass Set.univ = 1 := by
  induction p with
  | point k => simp [mass]
  | average p q hp hq => simp [mass, hp, hq]; norm_num

@[simp] theorem mass_empty (p : AlspachProbability K) : p.mass ∅ = 0 := by
  induction p with
  | point k => simp [mass]
  | average p q hp hq => simp [mass, hp, hq]

theorem mass_map (p : AlspachProbability K) (f : K → L) (U : Set L) :
    (p.map f).mass U = p.mass (f ⁻¹' U) := by
  induction p with
  | point k => rfl
  | average p q hp hq => simp [map, mass, hp, hq]

theorem restriction_single (U : Set K) (k : K) :
    JLMS.restrictionL1 U (lp.single 1 k (1 : 𝕜)) =
      if k ∈ U then lp.single 1 k 1 else 0 := by
  apply lp.ext
  funext j
  by_cases hj : j = k
  · subst j; by_cases hk : k ∈ U <;> simp [hk]
  · by_cases hk : k ∈ U <;> by_cases hjU : j ∈ U <;> simp [hk, hj, hjU]

theorem restriction_vector_norm_le_mass (p : AlspachProbability K) (U : Set K) :
    ‖JLMS.restrictionL1 U (p.vector (𝕜 := 𝕜))‖ ≤ p.mass U := by
  induction p with
  | point k =>
      rw [vector, restriction_single]
      by_cases hk : k ∈ U <;> simp [mass, hk, lp.norm_single]
  | average p q hp hq =>
      simp only [vector, map_smul, map_add, norm_smul, mass]
      have hh : ‖(1 / 2 : 𝕜)‖ = (1 / 2 : ℝ) := by norm_num [norm_div]
      rw [hh]
      have ha := norm_add_le (JLMS.restrictionL1 U (p.vector (𝕜 := 𝕜)))
        (JLMS.restrictionL1 U q.vector)
      linarith

def totalRead : lp (fun _ : K => 𝕜) 1 →L[𝕜] 𝕜 :=
  alspachSynthesis (fun _ : K => (1 : 𝕜)) 1 (fun _ => by simp)

theorem totalRead_norm_le : ‖totalRead (𝕜 := 𝕜) (K := K)‖ ≤ 1 :=
  alspachSynthesis_norm_le _ zero_le_one _

theorem totalRead_restriction_vector (p : AlspachProbability K) (U : Set K) :
    totalRead (JLMS.restrictionL1 U (p.vector (𝕜 := 𝕜))) = (p.mass U : 𝕜) := by
  induction p with
  | point k =>
      rw [vector, restriction_single]
      by_cases hk : k ∈ U <;> simp [mass, hk, totalRead]
  | average p q hp hq =>
      simp only [vector, map_smul, map_add, hp, hq, mass, smul_eq_mul,
        RCLike.ofReal_mul, RCLike.ofReal_add, RCLike.ofReal_div, RCLike.ofReal_one,
        RCLike.ofReal_ofNat]

theorem restriction_vector_norm_eq_mass (p : AlspachProbability K) (U : Set K) :
    ‖JLMS.restrictionL1 U (p.vector (𝕜 := 𝕜))‖ = p.mass U := by
  apply le_antisymm (restriction_vector_norm_le_mass p U)
  have hh := (totalRead (𝕜 := 𝕜) (K := K)).le_of_opNorm_le totalRead_norm_le
    (JLMS.restrictionL1 U (p.vector (𝕜 := 𝕜)))
  rw [totalRead_restriction_vector] at hh
  simpa only [one_mul, RCLike.norm_ofReal, abs_of_nonneg (p.mass_nonneg U)] using hh

theorem vector_norm (p : AlspachProbability K) : ‖p.vector (𝕜 := 𝕜)‖ = 1 := by
  have he : JLMS.restrictionL1 Set.univ (p.vector (𝕜 := 𝕜)) = p.vector := by
    ext k; simp
  simpa only [he, mass_univ] using p.restriction_vector_norm_eq_mass (𝕜 := 𝕜) Set.univ

theorem wolfeMass_probability [TopologicalSpace K] (M : JLMS.AtomicDualModel 𝕜 K)
    (p : AlspachProbability K) (U : Set K) :
    wolfeMass M (StrongDual.toWeakDual (M.representation.symm p.vector)) U = p.mass U := by
  change ‖JLMS.atomicRestriction M U (M.representation.symm p.vector)‖ = _
  rw [JLMS.atomicRestriction_norm, M.representation.apply_symm_apply]
  exact p.restriction_vector_norm_eq_mass U

end AlspachProbability
end Posets
