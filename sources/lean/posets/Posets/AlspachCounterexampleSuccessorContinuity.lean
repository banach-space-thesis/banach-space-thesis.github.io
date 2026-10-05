import Posets.AlspachCounterexampleSuccessorTopology
import Posets.AlspachCounterexampleGraftFunctions

/-! Weak-star continuity survives the successor construction. The proof
splits a test function into its continuous base values and deviations that
are uniformly small outside finitely many spines. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set Topology
namespace Posets
namespace AlspachPointedRows
variable {𝕜 K I X J : Type*} [RCLike 𝕜]
  [TopologicalSpace K] [TopologicalSpace I] [TopologicalSpace X] [TopologicalSpace J]
variable (F : AlspachPointedRows 𝕜 K I) (G : AlspachPointedRows 𝕜 X J)

def ContinuousRows : Prop := ∀ f : C(K, 𝕜), Continuous (fun i => (F.row i).eval f)

variable [CompactSpace K] [T2Space K] [CompactSpace X] [T2Space X]
  [CompactSpace J] [T2Space J]

def successorDeviation (f : C(F.SuccessorPointGraft G, 𝕜)) (i : I) (j : J) : 𝕜 :=
  (F.row i).eval (fun k => (G.row j).eval (fun x => f
    (alspachCompactGraftAttach Prod.fst (fun _ : K × I => X) (fun _ => G.point) (k, i) x) -
      f (alspachGraftBase _ _ k)))

theorem successorDeviation_continuous (hG : G.ContinuousRows)
    (f : C(F.SuccessorPointGraft G, 𝕜)) (i : I) :
    Continuous (F.successorDeviation G f i) := by
  apply AlspachProbability.continuous_eval
  intro k _
  exact hG ⟨_, (f.continuous.comp (alspachCompactGraftAttach_continuous _ _ _ (k, i))).sub
    continuous_const⟩

theorem successorDeviation_root (f : C(F.SuccessorPointGraft G, 𝕜)) (i : I) :
    F.successorDeviation G f i G.index = 0 := by
  simp [successorDeviation, G.row_root]

theorem successorDeviation_small (f : C(F.SuccessorPointGraft G, 𝕜))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset I, ∀ i ∉ s, ∀ j, ‖F.successorDeviation G f i j‖ ≤ ε := by
  let d (z : F.SuccessorPointGraft G) := f z - f (alspachGraftBase _ _ z.val.1)
  have hd : Continuous d := f.continuous.sub (f.continuous.comp
    ((alspachGraftBase_continuous _ _).comp (continuous_fst.comp continuous_subtype_val)))
  have hzero (k : K) : d (alspachGraftBase _ _ k) = 0 := by simp [d, alspachGraftBase]
  obtain ⟨s, hs⟩ := alspachGraft_finitely_many_large_spines Prod.fst
    (fun _ : K × I => {x : X // x ≠ G.point}) d hd hzero hε
  refine ⟨s.image Prod.snd, ?_⟩
  intro i hi j
  apply AlspachProbability.norm_eval_le
  intro k _
  apply AlspachProbability.norm_eval_le
  intro x _
  by_cases hx : x = G.point
  · subst x; simp only [alspachCompactGraftAttach_root, sub_self, norm_zero]; exact hε.le
  · have hki : (k, i) ∉ s := fun hk => hi (Finset.mem_image.mpr ⟨(k, i), hk, rfl⟩)
    have hh := (hs (k, i) hki ⟨x, hx⟩).le
    rw [alspachCompactGraftAttach_nonroot _ _ _ _ _ hx]
    exact hh

def successorDeviationCZero (hG : G.ContinuousRows) (f : C(F.SuccessorPointGraft G, 𝕜)) :
    JLMS.CZero 𝕜 (Σ _ : I, {j : J // j ≠ G.index}) :=
  alspachPuncturedSumCZero (fun _ : I => G.index) (F.successorDeviation G f)
    (F.successorDeviation_continuous G hG f) (F.successorDeviation_root G f)
    (fun _ hε => F.successorDeviation_small G f hε)

theorem topologicalSuccessor_continuous (hF : F.ContinuousRows) (hG : G.ContinuousRows) :
    (F.topologicalSuccessor G).ContinuousRows := by
  intro f
  let b : C(K, 𝕜) := ⟨fun k => f (alspachGraftBase _ _ k),
    f.continuous.comp (alspachGraftBase_continuous _ _)⟩
  let d := F.successorDeviationCZero G hG f
  let e := JLMS.extendCZeroOnePoint d
  have hb : Continuous (fun z : F.SuccessorIndexGraft G => (F.row z.val.1).eval b) :=
    (hF b).comp (continuous_fst.comp continuous_subtype_val)
  have he : Continuous (fun z : F.SuccessorIndexGraft G => e (alspachGraftProjection _ _ z)) :=
    e.continuous.comp (alspachGraftProjection_continuous _ _)
  have hEq : (fun z => ((F.topologicalSuccessor G).row z).eval f) =
      (fun z : F.SuccessorIndexGraft G => (F.row z.val.1).eval b +
        e (alspachGraftProjection _ _ z)) := by
    funext z
    rcases alspachGraft_cases id (fun _ : I => {j : J // j ≠ G.index}) z with
      ⟨i, rfl⟩ | ⟨⟨i, j⟩, rfl⟩
    · rw [F.topologicalSuccessor_eval_base G]
      change _ = _ + 0
      simp only [add_zero]
      rfl
    · rw [F.topologicalSuccessor_eval_spine G]
      change _ = (F.row i).eval (fun k => f (alspachGraftBase _ _ k)) +
        F.successorDeviation G f i j
      simp only [successorDeviation, AlspachProbability.eval_sub, AlspachProbability.eval_const]
      ring
  rw [hEq]
  exact hb.add he

end AlspachPointedRows
end Posets
