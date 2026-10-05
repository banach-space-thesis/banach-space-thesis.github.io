import Posets.BipartiteOperatorRealization
import Posets.MainStatements
import Mathlib.Topology.Algebra.Module.Basic

/-! Transfer through a strongly split quotient onto a constant bounded product. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open ThesisCommon TopologicalSpace
open scoped ENNReal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

def constantProductHead (C : Type) [NormedRing C] [NormedAlgebra 𝕜 C] :
    BoundedHom 𝕜 (NormedProduct (fun _ : ℕ => C)) C where
  toContinuousLinearMap :=
    ({ toFun := fun x => x 0
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : NormedProduct (fun _ : ℕ => C) →ₗ[𝕜] C).mkContinuous 1
      (fun x => by simpa only [one_mul] using lp.norm_apply_le_norm ENNReal.top_ne_zero x 0)
  map_mul' := fun _ _ => rfl

def constantProductSection (C : Type) [NormedRing C] [NormedAlgebra 𝕜 C] :
    C →L[𝕜] NormedProduct (fun _ : ℕ => C) :=
  lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => C) ∞ 0

@[simp] theorem constantProductHead_section (C : Type) [NormedRing C] [NormedAlgebra 𝕜 C]
    (c : C) : constantProductHead (𝕜 := 𝕜) C (constantProductSection (𝕜 := 𝕜) C c) = c :=
  lp.single_apply_self (E := fun _ : ℕ => C) ∞ 0 c

theorem finiteRank_hasSeparableRange {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (T : E →L[𝕜] F)
    (hT : FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)) : HasSeparableRange 𝕜 E F T := by
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional (LinearMap.range T.toLinearMap)).mpr hT
  change IsSeparable (LinearMap.range T.toLinearMap : Set F)
  rw [← hs]
  exact s.finite_toSet.isSeparable.span

set_option maxHeartbeats 800000 in
theorem discontinuous_hom_of_constantProduct_strongSplit
    {E C B : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedRing C] [NormedAlgebra 𝕜 C]
    [AddCommGroup B] [Module 𝕜 B] [Mul B] [TopologicalSpace B]
    (θ : BoundedHom 𝕜 (E →L[𝕜] E) (NormedProduct (fun _ : ℕ => C)))
    (ρ : BoundedHom 𝕜 (NormedProduct (fun _ : ℕ => C)) (E →L[𝕜] E))
    (hs : StrongSplit 𝕜 E (NormedProduct (fun _ : ℕ => C)) θ ρ)
    (Φ : C →ₗ[𝕜] B) (hΦ : IsMultiplicative 𝕜 Φ) (hnΦ : ¬ Continuous Φ) :
    ∃ Ψ : (E →L[𝕜] E) →ₗ[𝕜] B,
      IsMultiplicative 𝕜 Ψ ∧ Set.range Ψ = Set.range Φ ∧ ¬ Continuous Ψ ∧
      ∀ T, HasSeparableRange 𝕜 E E T → Ψ T = 0 := by
  let π := constantProductHead (𝕜 := 𝕜) C
  let j := constantProductSection (𝕜 := 𝕜) C
  let Ψ := Φ.comp (π.toContinuousLinearMap.toLinearMap.comp θ.toContinuousLinearMap.toLinearMap)
  have hj (c : C) : Ψ (ρ (j c)) = Φ c := by
    change Φ (π (θ (ρ (j c)))) = Φ c
    rw [hs.2.2]
    rw [constantProductHead_section]
  refine ⟨Ψ, ?_, ?_, ?_, ?_⟩
  · intro T S
    change Φ (π (θ (T*S))) = Φ (π (θ T)) * Φ (π (θ S))
    rw [θ.map_mul', π.map_mul', hΦ]
  · apply Set.Subset.antisymm
    · rintro _ ⟨T, rfl⟩
      exact ⟨π (θ T), rfl⟩
    · rintro _ ⟨c, rfl⟩
      exact ⟨ρ (j c), hj c⟩
  · intro hc
    apply hnΦ
    have h := hc.comp (ρ.continuous.comp j.continuous)
    exact h.congr (fun c => hj c)
  · intro T hT
    change Φ (π (θ T)) = 0
    rw [(hs.2.1 T).mpr hT]
    simp only [π, map_zero]

end Posets

