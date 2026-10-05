import JLMS.EllOneIndicatorDual
import JLMS.BoundedBelowDual

/-!
# The ℓ¹ dual is not separable

Indicator functionals indexed by all subsets of ℕ are separated by distance
one. A countable dense set would assign each of them a distinct point within
distance 1/3, giving an injection of the power set of ℕ into ℕ, contrary to
Cantor's theorem. Dual surjectivity then excludes an ℓ¹ embedding into any
normed space with separable dual.
-/

noncomputable section

open TopologicalSpace

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]

local instance ellOneDualNonseparableGroup : NormedAddCommGroup (ellOne 𝕜 →L[𝕜] 𝕜) := inferInstance
local instance ellOneDualNonseparableSpace : NormedSpace 𝕜 (ellOne 𝕜 →L[𝕜] 𝕜) := inferInstance

theorem ellOneIndicatorFunctional_dist_ge_one {S T : Set ℕ} (hne : S ≠ T) :
    1 ≤ dist (ellOneIndicatorFunctional (𝕜 := 𝕜) S) (ellOneIndicatorFunctional T) := by
  classical
  have hex : ∃ n, (n ∈ S ∧ n ∉ T) ∨ (n ∈ T ∧ n ∉ S) := by
    by_contra h
    push_neg at h
    apply hne
    ext n
    exact ⟨(h n).1, (h n).2⟩
  obtain ⟨n, hn⟩ := hex
  let u : ellOne 𝕜 := lp.single 1 n 1
  have hu : ‖u‖ = 1 := by
    rw [lp.norm_single (by norm_num : 0 < (1 : ENNReal)), norm_one]
  have hvalue : ‖(ellOneIndicatorFunctional (𝕜 := 𝕜) S - ellOneIndicatorFunctional (𝕜 := 𝕜) T) u‖ = 1 := by
    rcases hn with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;>
      simp [u, ContinuousLinearMap.sub_apply, ellOneIndicatorFunctional_single, hs, ht]
  rw [dist_eq_norm]
  have h : ‖(ellOneIndicatorFunctional (𝕜 := 𝕜) S - ellOneIndicatorFunctional (𝕜 := 𝕜) T) u‖ ≤
      ‖ellOneIndicatorFunctional (𝕜 := 𝕜) S - ellOneIndicatorFunctional (𝕜 := 𝕜) T‖ * ‖u‖ :=
    (ellOneIndicatorFunctional (𝕜 := 𝕜) S - ellOneIndicatorFunctional (𝕜 := 𝕜) T).le_opNorm u
  rw [hvalue, hu, mul_one] at h
  exact h

theorem ellOne_dual_not_separable : ¬SeparableSpace (ellOne 𝕜 →L[𝕜] 𝕜) := by
  classical
  intro hsep
  letI := hsep
  obtain ⟨D, hcnt, hdense⟩ := exists_countable_dense (α := ellOne 𝕜 →L[𝕜] 𝕜)
  choose d hd hdist using fun S : Set ℕ => hdense.exists_dist_lt
    (ellOneIndicatorFunctional (𝕜 := 𝕜) S) (by norm_num : (0 : ℝ) < 1 / 3)
  let g (S : Set ℕ) : D := ⟨d S, hd S⟩
  have hinj : Function.Injective g := by
    intro S T heq
    by_contra hne
    have he : d S = d T := congrArg Subtype.val heq
    have htriangle := dist_triangle (ellOneIndicatorFunctional (𝕜 := 𝕜) S) (d S)
      (ellOneIndicatorFunctional T)
    rw [he, dist_comm (d T)] at htriangle
    have hsep' := ellOneIndicatorFunctional_dist_ge_one (𝕜 := 𝕜) hne
    have hs := hdist S
    have ht := hdist T
    rw [he] at hs
    linarith
  letI : Countable D := hcnt.to_subtype
  have hc : Countable (Set ℕ) := hinj.countable
  obtain ⟨e⟩ := countable_iff_nonempty_embedding.mp hc
  exact Function.cantor_injective e e.injective

/-- A space with separable dual cannot contain an isomorphic copy of ℓ¹. -/
theorem not_containsEllOne_of_separable_dual {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [SeparableSpace (X →L[𝕜] 𝕜)] :
    ¬ContainsEllOne 𝕜 X := by
  rintro ⟨J, c, hc, hlower⟩
  exact ellOne_dual_not_separable (𝕜 := 𝕜) (dual_separable_of_bounded_below J hc hlower)

end JLMS
