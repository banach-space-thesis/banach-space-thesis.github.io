import BanachIsometric.Statements

/-!
# Metric isometries and passage to subspaces

These are proved reductions. They do not contain the finite-dimensional
geometric rigidity theorem needed to finish Corollary B.
-/

universe u

namespace BanachIsometric

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The norm-preserving real-linear version of the paper's metric hypothesis.
Restriction of scalars imposes no complex-linearity on the maps. -/
def RealLinearSubspaceHomogeneity (n : ℕ) : Prop :=
  ∀ (E F : Submodule 𝕜 X),
    Module.rank 𝕜 E = (n : Cardinal) →
    Module.rank 𝕜 F = (n : Cardinal) →
    Nonempty (RestrictScalars ℝ 𝕜 E ≃ₗᵢ[ℝ] RestrictScalars ℝ 𝕜 F)

/-- Mazur--Ulam supplies precisely real-linearity, even if the given metric
isometry does not fix zero. Completeness is not required. -/
theorem metricSubspaceHomogeneity_iff_realLinear (n : ℕ) :
    MetricSubspaceHomogeneity 𝕜 X n ↔
      RealLinearSubspaceHomogeneity (𝕜 := 𝕜) (X := X) n := by
  constructor
  · intro h E F hE hF
    obtain ⟨e⟩ := h E F hE hF
    exact ⟨(show RestrictScalars ℝ 𝕜 E ≃ᵢ RestrictScalars ℝ 𝕜 F from e).toRealLinearIsometryEquiv⟩
  · intro h E F hE hF
    obtain ⟨e⟩ := h E F hE hF
    exact ⟨e.toIsometryEquiv⟩

/-- Flatten a subspace of a subspace without changing its norm. -/
noncomputable def nestedSubmoduleIsometry (Y : Submodule 𝕜 X) (E : Submodule 𝕜 Y) :
    E ≃ₗᵢ[𝕜] E.map Y.subtype :=
  { Submodule.equivMapOfInjective Y.subtype Y.subtype_injective E with
    norm_map' := fun _ => rfl }

/-- The fixed-dimension metric hypothesis is inherited by every scalar subspace. -/
theorem MetricSubspaceHomogeneity.submodule {n : ℕ}
    (h : MetricSubspaceHomogeneity 𝕜 X n) (Y : Submodule 𝕜 X) :
    MetricSubspaceHomogeneity 𝕜 Y n := by
  intro E F hE hF
  let e := nestedSubmoduleIsometry Y E
  let f := nestedSubmoduleIsometry Y F
  have hE' : Module.rank 𝕜 (E.map Y.subtype) = (n : Cardinal) :=
    e.toLinearEquiv.rank_eq.symm.trans hE
  have hF' : Module.rank 𝕜 (F.map Y.subtype) = (n : Cardinal) :=
    f.toLinearEquiv.rank_eq.symm.trans hF
  obtain ⟨g⟩ := h (E.map Y.subtype) (F.map Y.subtype) hE' hF'
  exact ⟨(e.toIsometryEquiv.trans g).trans f.symm.toIsometryEquiv⟩

end BanachIsometric
