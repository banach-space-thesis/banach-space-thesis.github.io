import JLMS.NormalizedBlocks

/-!
# Composition of ordered normalized block systems

Finite outer blocks combine disjoint inner blocks. Their coefficient mass
remains exactly one: disjointness prevents cancellation between inner
supports. Ordering is preserved. This supplies the nested blocking operation
used by asymptotic-radius stabilization.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
attribute [local instance] Classical.decEq

def blockCompositeSupport (b c : NormalizedBlockSystem 𝕜) (n : ℕ) : Finset ℕ :=
  (c.support n).biUnion b.support

def blockCompositeCoefficient (b c : NormalizedBlockSystem 𝕜) (n k : ℕ) : 𝕜 :=
  ∑ j ∈ c.support n, c.coefficient n j *
    (if k ∈ b.support j then b.coefficient j k else 0)

theorem blockCompositeCoefficient_at (b c : NormalizedBlockSystem 𝕜) (n j k : ℕ)
    (hj : j ∈ c.support n) (hk : k ∈ b.support j) :
    blockCompositeCoefficient b c n k = c.coefficient n j * b.coefficient j k := by
  rw [blockCompositeCoefficient, Finset.sum_eq_single j]
  · simp [hk]
  · intro i hi hij
    have hki : k ∉ b.support i := fun h => Finset.disjoint_left.mp (b.disjoint hij) h hk
    simp [hki]
  · exact fun h => (h hj).elim

theorem blockComposite_mass_one (b c : NormalizedBlockSystem 𝕜) (n : ℕ) :
    ∑ k ∈ blockCompositeSupport b c n, ‖blockCompositeCoefficient b c n k‖ = 1 := by
  rw [blockCompositeSupport, Finset.sum_biUnion (fun i hi j hj hij => b.disjoint hij)]
  calc
    _ = ∑ j ∈ c.support n, ∑ k ∈ b.support j, ‖c.coefficient n j‖ * ‖b.coefficient j k‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [blockCompositeCoefficient_at b c n j k hj hk, norm_mul]
    _ = ∑ j ∈ c.support n, ‖c.coefficient n j‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum, b.mass_one, mul_one]
    _ = 1 := c.mass_one n

def NormalizedBlockSystem.compose (b c : NormalizedBlockSystem 𝕜) : NormalizedBlockSystem 𝕜 where
  support := blockCompositeSupport b c
  coefficient := blockCompositeCoefficient b c
  mass_one := blockComposite_mass_one b c
  ordered := by
    intro n m hnm i hi j hj
    obtain ⟨p, hp, hip⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨q, hq, hjq⟩ := Finset.mem_biUnion.mp hj
    exact b.ordered p q (c.ordered n m hnm p hp q hq) i hip j hjq

theorem NormalizedBlockSystem.compose_applyDual {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (b c : NormalizedBlockSystem 𝕜) (f : ℕ → (X →L[𝕜] 𝕜)) (n : ℕ) :
    (b.compose c).applyDual f n = c.applyDual (b.applyDual f) n := by
  change (∑ k ∈ blockCompositeSupport b c n, blockCompositeCoefficient b c n k • f k) = _
  rw [blockCompositeSupport, Finset.sum_biUnion (fun i hi j hj hij => b.disjoint hij)]
  change _ = ∑ j ∈ c.support n, c.coefficient n j • (∑ k ∈ b.support j, b.coefficient j k • f k)
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [blockCompositeCoefficient_at b c n j k hj hk, mul_smul]

def NormalizedBlockSystem.units : NormalizedBlockSystem 𝕜 where
  support n := {n}
  coefficient _ _ := 1
  mass_one := by intro n; simp
  ordered := by
    intro n m hnm i hi j hj
    simp only [Finset.mem_singleton] at hi hj
    simpa [hi, hj] using hnm

@[simp] theorem NormalizedBlockSystem.units_applyDual {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (f : ℕ → (X →L[𝕜] 𝕜)) (n : ℕ) :
    (NormalizedBlockSystem.units (𝕜 := 𝕜)).applyDual f n = f n := by
  simp [NormalizedBlockSystem.applyDual, NormalizedBlockSystem.units, dualFiniteBlock]

end JLMS
