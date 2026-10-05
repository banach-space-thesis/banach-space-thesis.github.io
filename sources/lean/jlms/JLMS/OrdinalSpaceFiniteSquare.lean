import JLMS.OrdinalSpaceInitialFiniteReduction

/-!
# Finite powers of a space isomorphic to its square

The finite-quotient reduction also applies when the initial-ordinal space
is isomorphic to its square. This treats countable and singular initial
ordinals once their base square equivalences have been constructed.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

def piProductContinuousLinearEquiv (I E F : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
    (I → E × F) ≃L[𝕜] (I → E) × (I → F) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := (continuous_pi (fun i => (continuous_apply i).fst)).prodMk
    (continuous_pi (fun i => (continuous_apply i).snd))
  continuous_invFun := continuous_pi (fun i =>
    ((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd))

def finitePowerSquareEquiv (I E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (e : E ≃L[𝕜] E × E) :
    (I → E) ≃L[𝕜] (I → E) × (I → E) :=
  (ContinuousLinearEquiv.piCongrRight (fun _ : I => e)).trans
    (piProductContinuousLinearEquiv I E E)

def ordinalSpaceFiniteMultipleSquareEquiv (κ : Ordinal.{u}) (hκ : Ordinal.omega0 ≤ κ)
    (n : ℕ) (e : OrdinalC 𝕜 κ ≃L[𝕜] OrdinalC 𝕜 κ × OrdinalC 𝕜 κ) :
    OrdinalC 𝕜 (κ * ((n + 1 : ℕ) : Ordinal)) ≃L[𝕜]
      OrdinalC 𝕜 (κ * ((n + 1 : ℕ) : Ordinal)) × OrdinalC 𝕜 (κ * ((n + 1 : ℕ) : Ordinal)) :=
  let d := ordinalSpaceFinitePower (𝕜 := 𝕜) κ hκ n
  d.trans ((finitePowerSquareEquiv (Fin (n + 1)) (OrdinalC 𝕜 κ) e).trans
    (d.symm.prodCongr d.symm))

theorem ordinalSpaceReduction_of_initial_finiteQuotient_of_square
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (e : OrdinalC 𝕜 c.ord ≃L[𝕜] OrdinalC 𝕜 c.ord × OrdinalC 𝕜 c.ord)
    (α : Ordinal.{u}) (hlo : c.ord ≤ α) (hhi : α < c.ord * Ordinal.omega0) :
    OrdinalSpaceReduction 𝕜 α := by
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  have hα := hκ.trans hlo
  obtain ⟨n, ρ, hρ, heq⟩ := exists_initial_finite_quotient_remainder c hc α hlo hhi
  have hmul : c.ord ≤ c.ord * ((n + 1 : ℕ) : Ordinal) :=
    Ordinal.le_mul_left _ (by exact_mod_cast Nat.succ_pos n)
  let d : OrdinalC 𝕜 α ≃L[𝕜] OrdinalC 𝕜 (c.ord * ((n + 1 : ℕ) : Ordinal)) :=
    (ordinalSpaceCongrIsometry (𝕜 := 𝕜) heq).toContinuousLinearEquiv.trans
      (ordinalSpaceSmallRemainder c hc _ ρ hmul hρ)
  refine Or.inr (Or.inl ⟨hα, ⟨?_⟩⟩)
  exact d.trans ((ordinalSpaceFiniteMultipleSquareEquiv c.ord hκ n e).trans
    ((d.symm.prodCongr d.symm).trans
      (ordinalSpaceDoubleIsometry (𝕜 := 𝕜) α hα).symm.toContinuousLinearEquiv))

end JLMS
