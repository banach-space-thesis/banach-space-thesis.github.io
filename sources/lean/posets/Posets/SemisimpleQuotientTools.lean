import Posets.QuotientAlgebraEquiv
import Posets.MainStatements
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Quotient coordinates and finite-prefix coordinates for semisimple targets. -/

noncomputable section
open ThesisCommon
open scoped ENNReal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

def strongSplitQuotientLinearEquiv {E C : Type}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C]
    (θ : BoundedHom 𝕜 (E →L[𝕜] E) C) (ρ : BoundedHom 𝕜 C (E →L[𝕜] E))
    (hs : StrongSplit 𝕜 E C θ ρ) : SeparableQuotient 𝕜 E ≃ₗ[𝕜] C := by
  let S := JFA.separableRangeSubmodule (𝕜 := 𝕜) (E := E) (F := E)
  let f : SeparableQuotient 𝕜 E →ₗ[𝕜] C := S.liftQ θ.toContinuousLinearMap.toLinearMap
    (fun T hT => (hs.2.1 T).mpr hT)
  have hi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    obtain ⟨T, rfl⟩ := quotientMap_surjective 𝕜 E x
    apply (quotientMap_eq_zero_iff 𝕜 E T).mpr
    exact (hs.2.1 T).mp hx
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨T, hT⟩ := hs.1 c
    exact ⟨quotientMap 𝕜 E T, hT⟩
  exact LinearEquiv.ofBijective f ⟨hi, hsurj⟩

@[simp] theorem strongSplitQuotientLinearEquiv_apply {E C : Type}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C]
    (θ : BoundedHom 𝕜 (E →L[𝕜] E) C) (ρ : BoundedHom 𝕜 C (E →L[𝕜] E))
    (hs : StrongSplit 𝕜 E C θ ρ) (T : E →L[𝕜] E) :
    strongSplitQuotientLinearEquiv θ ρ hs (quotientMap 𝕜 E T) = θ T := rfl

/-- An ℓ∞ product with trivial factors past n is precisely its finite prefix. -/
def normedProductPrefixLinearEquiv (C : ℕ → Type)
    [∀ m, NormedRing (C m)] [∀ m, NormedAlgebra 𝕜 (C m)]
    (n : ℕ) (hz : ∀ m, n ≤ m → Subsingleton (C m)) :
    NormedProduct C ≃ₗ[𝕜] (Π i : Fin n, C i.val) := by
  classical
  let ext (f : Π i : Fin n, C i.val) : NormedProduct C :=
    ⟨fun m => if h : m < n then f ⟨m, h⟩ else 0,
      memℓp_infty ⟨‖f‖, by
        rintro r ⟨m, rfl⟩
        by_cases h : m < n
        · simpa only [dif_pos h] using norm_le_pi_norm f ⟨m, h⟩
        · simp only [dif_neg h, norm_zero]
          exact norm_nonneg f⟩⟩
  exact
    { toFun := fun x i => x i.val
      invFun := ext
      left_inv := by
        intro x
        apply lp.ext
        funext m
        by_cases h : m < n
        · simp [ext, h]
        · letI := hz m (Nat.le_of_not_gt h)
          exact Subsingleton.elim _ _
      right_inv := by
        intro f
        funext i
        simp [ext, i.isLt]
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }

theorem normedProductPrefixLinearEquiv_map_mul (C : ℕ → Type)
    [∀ m, NormedRing (C m)] [∀ m, NormedAlgebra 𝕜 (C m)]
    (n : ℕ) (hz : ∀ m, n ≤ m → Subsingleton (C m)) (x y : NormedProduct C) :
    normedProductPrefixLinearEquiv (𝕜 := 𝕜) C n hz (x * y) =
      normedProductPrefixLinearEquiv (𝕜 := 𝕜) C n hz x *
        normedProductPrefixLinearEquiv (𝕜 := 𝕜) C n hz y := rfl

end Posets
