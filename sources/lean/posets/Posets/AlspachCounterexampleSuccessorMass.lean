import Posets.AlspachCounterexampleSuccessorTopology
import Posets.AlspachCounterexampleMassCalculus
import Posets.AlspachCounterexampleGraftClosedSets

/-! The exact two-branch mass formula at a successor and the doubling of
the threshold away from the distinguished base point. Closed parent windows
are essential here, as in the closure condition in Wolfe's definition. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set
namespace Posets
variable {K : Type*}

theorem alspachBaseRow_eval_real (p x : K) (f : K → ℝ) :
    (alspachBaseRow p x).eval f = (1 / 2 : ℝ) * (f x + f p) := by
  by_cases hx : x = p
  · subst x; simp [alspachBaseRow]; ring
  · simp [alspachBaseRow, hx]

theorem alspachBaseRow_mass (p x : K) (U : Set K) :
    (alspachBaseRow p x).mass U =
      (1 / 2 : ℝ) * ((if x ∈ U then 1 else 0) + (if p ∈ U then 1 else 0)) := by
  rw [AlspachProbability.mass_eq_eval_indicator, alspachBaseRow_eval_real]

theorem alspachBaseRow_mass_le_half {p x : K} {U : Set K} (hp : p ∉ U) :
    (alspachBaseRow p x).mass U ≤ 1 / 2 := by
  rw [alspachBaseRow_mass]
  by_cases hx : x ∈ U <;> simp [hp, hx] <;> norm_num

namespace AlspachPointedRows
variable {𝕜 X J : Type*} [RCLike 𝕜]
  [TopologicalSpace K] [TopologicalSpace X] [TopologicalSpace J]
  [CompactSpace X] [T2Space X]
variable (p : K) (G : AlspachPointedRows 𝕜 X J)

abbrev baseAttach (k i : K) : X → (base (𝕜 := 𝕜) p).SuccessorPointGraft G :=
  alspachCompactGraftAttach Prod.fst (fun _ : K × K => X) (fun _ => G.point) (k, i)

theorem baseSuccessor_mass_spine (i : K) (j : {j : J // j ≠ G.index})
    (U : Set ((base (𝕜 := 𝕜) p).SuccessorPointGraft G)) :
    (((base (𝕜 := 𝕜) p).topologicalSuccessor G).row
      (alspachGraftSpine _ _ ⟨i, j⟩)).mass U =
      (1 / 2 : ℝ) * ((G.row j).mass (baseAttach p G i i ⁻¹' U) +
        (G.row j).mass (baseAttach p G p i ⁻¹' U)) := by
  change (((alspachBaseRow p i).bind (fun k => (G.row j).map ((base p).attach G k i))).map
    ((base p).successorPointEquiv G)).mass U = _
  rw [AlspachProbability.mass_map, AlspachProbability.mass_bind]
  simp_rw [AlspachProbability.mass_map]
  have he (k : K) : (base (𝕜 := 𝕜) p).attach G k i ⁻¹'
      ((base p).successorPointEquiv G ⁻¹' U) = baseAttach p G k i ⁻¹' U := by
    ext x
    change (base p).successorPointEquiv G ((base p).attach G k i x) ∈ U ↔ _
    rw [successorPointEquiv_attach]
    rfl
  simp_rw [he]
  exact alspachBaseRow_eval_real p i _

theorem baseSuccessor_mass_doubling [CompactSpace K] [T2Space K]
    (C : Set ((base (𝕜 := 𝕜) p).SuccessorPointGraft G)) (hC : IsClosed C)
    (hp : alspachGraftBase _ _ p ∉ C) :
    ∃ s : Finset K, ∀ i ∉ s, ∀ j : {j : J // j ≠ G.index}, ∀ U ⊆ C,
      (((base (𝕜 := 𝕜) p).topologicalSuccessor G).row
        (alspachGraftSpine _ _ ⟨i, j⟩)).mass U =
        (1 / 2 : ℝ) * (G.row j).mass (baseAttach p G i i ⁻¹' U) := by
  obtain ⟨s, hs⟩ := alspachGraft_closed_excludes_base_finite_spines Prod.fst
    (fun _ : K × K => {x : X // x ≠ G.point}) C hC p hp
  refine ⟨s.image Prod.snd, ?_⟩
  intro i hi j U hUC
  have hpi : (p, i) ∉ s := fun h => hi (Finset.mem_image.mpr ⟨(p, i), h, rfl⟩)
  have hm : (G.row j).mass (baseAttach p G p i ⁻¹' U) = 0 := by
    apply AlspachProbability.mass_eq_zero
    intro x _ hxU
    have hxC := hUC hxU
    by_cases hx : x = G.point
    · subst x
      exact hp (by simpa only [baseAttach, alspachCompactGraftAttach_root] using hxC)
    · exact hs (p, i) hpi rfl ⟨x, hx⟩ (by
        simpa only [baseAttach, alspachCompactGraftAttach_nonroot Prod.fst (fun _ : K × K => X) (fun _ => G.point) (p, i) x hx] using hxC)
  rw [baseSuccessor_mass_spine, hm, add_zero]

end AlspachPointedRows
end Posets

