import Posets.AlspachCounterexampleGraft

/-! Each attached spine, completed by its anchor point, is an actual copy
of its one-point compactification. This supplies the closed embeddings used
to compare Cantor--Bendixson derivatives in the recursive construction. -/

noncomputable section
open Set Topology
open scoped OnePoint
namespace Posets
variable {K I : Type*} [TopologicalSpace K]
  (anchor : I → K) (X : I → Type*) [∀ i, TopologicalSpace (X i)]

def alspachGraftCompletedSpine (i : I) (x : OnePoint (X i)) : AlspachGraft anchor X :=
  ⟨(anchor i, OnePoint.map (Sigma.mk i) x), by
    intro z hz
    cases x with
    | infty => exact (OnePoint.coe_ne_infty z hz.symm).elim
    | coe x =>
        have he : (⟨i, x⟩ : Σ i, X i) = z := OnePoint.coe_injective hz
        exact congrArg (fun w : Σ i, X i => anchor w.1) he⟩

@[simp] theorem alspachGraftCompletedSpine_infty (i : I) :
    alspachGraftCompletedSpine anchor X i ∞ = alspachGraftBase anchor X (anchor i) := rfl

@[simp] theorem alspachGraftCompletedSpine_coe (i : I) (x : X i) :
    alspachGraftCompletedSpine anchor X i x = alspachGraftSpine anchor X ⟨i, x⟩ := rfl

theorem alspachGraftCompletedSpine_injective (i : I) :
    Function.Injective (alspachGraftCompletedSpine anchor X i) := by
  intro x y h
  have he := congrArg (alspachGraftProjection anchor X) h
  cases x <;> cases y <;> simp_all [alspachGraftCompletedSpine, alspachGraftProjection]

theorem alspachGraftCompletedSpine_continuous [∀ i, T2Space (X i)] (i : I) :
    Continuous (alspachGraftCompletedSpine anchor X i) := by
  have hm : Continuous (OnePoint.map (@Sigma.mk I X i)) :=
    OnePoint.continuous_map continuous_sigmaMk (by
      rw [Filter.coclosedCompact_eq_cocompact, Filter.coclosedCompact_eq_cocompact]
      exact IsClosedEmbedding.sigmaMk.tendsto_cocompact)
  have hk : Continuous (fun _ : OnePoint (X i) => anchor i) := continuous_const
  exact (hk.prodMk hm).subtype_mk _

theorem alspachGraftCompletedSpine_isClosedEmbedding [T2Space K]
    [∀ i, T2Space (X i)] [∀ i, LocallyCompactSpace (X i)] (i : I) :
    IsClosedEmbedding (alspachGraftCompletedSpine anchor X i) :=
  (alspachGraftCompletedSpine_continuous anchor X i).isClosedEmbedding
    (alspachGraftCompletedSpine_injective anchor X i)

end Posets
