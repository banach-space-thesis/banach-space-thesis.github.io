import ThesisCommon.Analysis.JamesSequenceSpaceComplete
import ThesisCommon.Analysis.SequencePrefixes

/-! The actual initial-coordinate projections on James space are
contractive. To retain the endpoint term, move the later nodes of each
finite path to infinity and use null convergence of the original sequence.
This proves the bound for the genuine variation norm, including p = infinity.
-/
noncomputable section
open Filter Topology
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon

/-- Keep path nodes at most k and translate all later nodes to the right. -/
def JamesPath.shiftTail (s : JamesPath) (k m : ℕ) : JamesPath where
  length := s.length
  index j := if s.index j ≤ k then s.index j else m + s.index j
  strictMono := by
    intro i j hij
    have h := s.strictMono hij
    dsimp
    split_ifs <;> omega

variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent}

theorem james_shiftTail_path_tendsto (x : JamesSequenceSpace 𝕜 p)
    (s : JamesPath) (k : ℕ) :
    Tendsto (fun m => jamesPathMap 𝕜 p (s.shiftTail k m) x.val) atTop
      (𝓝 (jamesPathMap 𝕜 p s (cZeroPrefix k x.val))) := by
  have hx (n : ℕ) :
      Tendsto (fun m => x (if n ≤ k then n else m + n)) atTop
        (𝓝 (if n ≤ k then x n else 0)) := by
    by_cases hn : n ≤ k
    · simp only [if_pos hn]
      exact tendsto_const_nhds
    · simp only [if_neg hn]
      exact x.tendsto_zero.comp (tendsto_add_atTop_nat n)
  have ht : Tendsto
      (fun m => fun j : Fin s.length =>
        x (if s.index j.castSucc ≤ k then s.index j.castSucc else m + s.index j.castSucc) -
          x (if s.index j.succ ≤ k then s.index j.succ else m + s.index j.succ)) atTop
      (𝓝 (fun j : Fin s.length =>
        (if s.index j.castSucc ≤ k then x (s.index j.castSucc) else 0) -
          (if s.index j.succ ≤ k then x (s.index j.succ) else 0))) :=
    tendsto_pi_nhds.mpr (fun j => (hx (s.index j.castSucc)).sub (hx (s.index j.succ)))
  exact ((PiLp.continuous_toLp p.val (fun _ : Fin s.length => 𝕜)).tendsto _).comp ht

theorem james_initial_path_norm_le (x : JamesSequenceSpace 𝕜 p) (k : ℕ) (s : JamesPath) :
    ‖jamesPathMap 𝕜 p s (cZeroPrefix k x.val)‖ ≤ ‖x‖ :=
  le_of_tendsto (james_shiftTail_path_tendsto x s k).norm
    (Eventually.of_forall (fun m => x.path_norm_le (s.shiftTail k m)))

namespace JamesSequenceSpace

/-- Initial truncation in the actual James norm. Coordinates 0 through k
are retained; all later coordinates vanish. -/
def initialValue (k : ℕ) (x : JamesSequenceSpace 𝕜 p) : JamesSequenceSpace 𝕜 p :=
  ⟨cZeroPrefix k x.val, ⟨‖x‖, by
    rintro _ ⟨s, rfl⟩
    exact james_initial_path_norm_le x k s⟩⟩

@[simp] theorem initialValue_apply (k n : ℕ) (x : JamesSequenceSpace 𝕜 p) :
    initialValue k x n = if n ≤ k then x n else 0 := rfl

theorem norm_initialValue_le (k : ℕ) (x : JamesSequenceSpace 𝕜 p) :
    ‖initialValue k x‖ ≤ ‖x‖ := norm_le (james_initial_path_norm_le x k)

def initial (k : ℕ) : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p :=
  LinearMap.mkContinuous
    { toFun := initialValue k
      map_add' := by
        intro x y
        ext n
        by_cases hn : n ≤ k <;> simp [hn]
      map_smul' := by
        intro a x
        ext n
        by_cases hn : n ≤ k <;> simp [hn] }
    1 (fun x => by simpa only [one_mul] using norm_initialValue_le k x)

@[simp] theorem initial_apply (k n : ℕ) (x : JamesSequenceSpace 𝕜 p) :
    initial (𝕜 := 𝕜) (p := p) k x n = if n ≤ k then x n else 0 := rfl

theorem norm_initial_le (k : ℕ) : ‖initial (𝕜 := 𝕜) (p := p) k‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem initial_idempotent (k : ℕ) :
    (initial (𝕜 := 𝕜) (p := p) k).comp (initial k) = initial k := by
  apply ContinuousLinearMap.ext
  intro x
  ext n
  by_cases hn : n ≤ k <;> simp [hn]

def tail (k : ℕ) : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p :=
  ContinuousLinearMap.id 𝕜 _ - initial k

@[simp] theorem tail_apply (k n : ℕ) (x : JamesSequenceSpace 𝕜 p) :
    tail (𝕜 := 𝕜) (p := p) k x n = if n ≤ k then 0 else x n := by
  change x n - (if n ≤ k then x n else 0) = _
  by_cases hn : n ≤ k <;> simp [hn]

theorem norm_tail_le (k : ℕ) : ‖tail (𝕜 := 𝕜) (p := p) k‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans (by
    have h := add_le_add (ContinuousLinearMap.norm_id_le (𝕜 := 𝕜)
      (E := JamesSequenceSpace 𝕜 p)) (norm_initial_le (𝕜 := 𝕜) (p := p) k)
    norm_num at h ⊢
    exact h)

end JamesSequenceSpace
end ThesisCommon
