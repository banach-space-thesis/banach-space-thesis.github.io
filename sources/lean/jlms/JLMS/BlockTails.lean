import JLMS.NestedBlocks

/-!
# Removing finite prefixes of dual sequences and coefficient blocks

Eventual bounds and their asymptotic radius are invariant under finite
shifts. Blocks supported beyond a fixed input prefix can be translated
back to zero without changing their normalization or order.
-/

noncomputable section
open Filter Topology
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem dualEventualBound_shift_iff (f : ℕ → (X →L[𝕜] 𝕜)) (m : ℕ) (r : ℝ) :
    DualEventualBound (fun n => f (n + m)) r ↔ DualEventualBound f r := by
  constructor
  · intro h x ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h x ε hε)
    apply eventually_atTop.mpr
    refine ⟨N + m, fun n hn => ?_⟩
    have hm : m ≤ n := by omega
    have h := hN (n - m) (by omega)
    simpa only [Nat.sub_add_cancel hm] using h
  · intro h x ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h x ε hε)
    exact eventually_atTop.mpr ⟨N, fun n hn => hN (n + m) (by omega)⟩

theorem dualAsymptoticRadius_shift (f : ℕ → (X →L[𝕜] 𝕜)) (m : ℕ) :
    dualAsymptoticRadius (fun n => f (n + m)) = dualAsymptoticRadius f := by
  unfold dualAsymptoticRadius
  congr 1
  ext r
  exact and_congr_right (fun _ => dualEventualBound_shift_iff f m r)

attribute [local instance] Classical.decEq

def NormalizedBlockSystem.shiftInput (b : NormalizedBlockSystem 𝕜) (m : ℕ)
    (hm : ∀ n k, k ∈ b.support n → m ≤ k) : NormalizedBlockSystem 𝕜 where
  support n := (b.support n).image (fun k => k - m)
  coefficient n k := b.coefficient n (k + m)
  mass_one := by
    intro n
    rw [Finset.sum_image]
    · convert b.mass_one n using 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.sub_add_cancel (hm n k hk)]
    · intro i hi j hj hij
      change i - m = j - m at hij
      have hmi := hm n i hi
      have hmj := hm n j hj
      omega
  ordered := by
    intro n p hnp i hi j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
    have h := b.ordered n p hnp k hk l hl
    have hmk := hm n k hk
    have hml := hm p l hl
    omega

theorem NormalizedBlockSystem.shiftInput_applyDual
    (b : NormalizedBlockSystem 𝕜) (m : ℕ)
    (hm : ∀ n k, k ∈ b.support n → m ≤ k)
    (f : ℕ → (X →L[𝕜] 𝕜)) (n : ℕ) :
    (b.shiftInput m hm).applyDual f n = b.applyDual (fun k => f (k - m)) n := by
  change (∑ k ∈ (b.support n).image (fun k => k - m), b.coefficient n (k + m) • f k) = _
  rw [Finset.sum_image]
  · change _ = ∑ k ∈ b.support n, b.coefficient n k • f (k - m)
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.sub_add_cancel (hm n k hk)]
  · intro i hi j hj hij
    change i - m = j - m at hij
    have hmi := hm n i hi
    have hmj := hm n j hj
    omega

end JLMS
