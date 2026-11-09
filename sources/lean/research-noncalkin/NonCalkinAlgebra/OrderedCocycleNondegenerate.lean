import NonCalkinAlgebra.OrderedCocycle

noncomputable section
set_option autoImplicit false
universe u v

namespace NonCalkinAlgebra.FiniteSupportCocycle

theorem pairing_left_single {I : Type u} {J : Type v} (m : I → J → ZMod 2)
    (i : I) (y : J →₀ ZMod 2) :
    pairing m (Finsupp.single i 1) y = y.sum (fun j b => b * m i j) := by
  simp [pairing, Finsupp.linearCombination_apply, smul_eq_mul]

theorem pairing_right_single {I : Type u} {J : Type v} (m : I → J → ZMod 2)
    (x : I →₀ ZMod 2) (j : J) :
    pairing m x (Finsupp.single j 1) = x.sum (fun i a => a * m i j) := by
  classical
  have hs : (Finsupp.single j (1 : ZMod 2)).support = {j} :=
    Finsupp.support_single_ne_zero _ one_ne_zero
  simp [pairing, Finsupp.linearCombination_apply, Finsupp.sum, hs, smul_eq_mul]

end NonCalkinAlgebra.FiniteSupportCocycle

namespace NonCalkinAlgebra.OrderedCocycle
open FiniteSupportCocycle
variable (Λ : Type u) [LinearOrder Λ]

@[simp] theorem pairing_diagonal_left (i : Λ × ℕ) (y : (Λ × ℕ) →₀ ZMod 2) :
    pairing (diagonal Λ) (Finsupp.single i 1) y = y i := by
  classical
  rw [pairing_left_single]
  calc
    _ = y i * diagonal Λ i i := Finsupp.sum_eq_single i
      (fun j _ hji => by simp [diagonal, Ne.symm hji]) (by simp)
    _ = y i := by simp [diagonal]

@[simp] theorem pairing_diagonal_right (x : (Λ × ℕ) →₀ ZMod 2) (i : Λ × ℕ) :
    pairing (diagonal Λ) x (Finsupp.single i 1) = x i := by
  classical
  rw [pairing_right_single]
  calc
    _ = x i * diagonal Λ i i := Finsupp.sum_eq_single i
      (fun j _ hji => by simp [diagonal, hji]) (by simp)
    _ = x i := by simp [diagonal]

/-- The alternating form controlling commutation of the signed shifts. -/
def alternating (x y : Group Λ) : ZMod 2 := cocycle Λ x y + cocycle Λ y x

@[simp] theorem alternating_v (x : Group Λ) (ξ : Λ) (n : ℕ) :
    alternating Λ x (v Λ ξ n) = x.2 (ξ, n) := by
  simpa [alternating, cocycle, v, crossPairing] using pairing_diagonal_left Λ (ξ, n) x.2

@[simp] theorem alternating_w (x : Group Λ) (ξ : Λ) (n : ℕ) :
    alternating Λ x (w Λ ξ n) = x.1.1 (ξ, n) +
      x.1.2.sum (fun η a => a * (if ξ ≤ η then 1 else 0)) := by
  simpa [alternating, cocycle, w, crossPairing, orderEntry] using
    congrArg (fun t : ZMod 2 => x.1.1 (ξ, n) + t)
      (pairing_right_single (orderEntry Λ) x.1.2 (ξ, n))

/-- No nonzero finite-support binary vector commutes with every vector.
The fresh natural coordinate is essential for detecting a nonzero U part. -/
theorem alternating_nondegenerate (x : Group Λ)
    (hx : ∀ y : Group Λ, alternating Λ x y = 0) : x = 0 := by
  classical
  have hW : x.2 = 0 := by
    apply Finsupp.ext
    intro i
    simpa only [alternating_v] using hx (v Λ i.1 i.2)
  have hU : x.1.2 = 0 := by
    by_contra hne
    have hS : x.1.2.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
    let ξ : Λ := x.1.2.support.max' hS
    have hξ : ξ ∈ x.1.2.support := Finset.max'_mem _ _
    have hmax : ∀ η ∈ x.1.2.support, η ≤ ξ := fun η hη => Finset.le_max' _ η hη
    obtain ⟨n, _, hn⟩ := (Set.infinite_univ : (Set.univ : Set ℕ).Infinite).exists_notMem_finset
      (x.1.1.support.image Prod.snd)
    have hV : x.1.1 (ξ, n) = 0 := by
      by_contra hv
      exact hn (Finset.mem_image.mpr ⟨(ξ, n), Finsupp.mem_support_iff.mpr hv, rfl⟩)
    have hsum : x.1.2.sum (fun η a => a * (if ξ ≤ η then 1 else 0)) = x.1.2 ξ := by
      calc
        _ = x.1.2 ξ * (if ξ ≤ ξ then 1 else 0) := Finsupp.sum_eq_single ξ
          (fun η hη hneq => by
            have hnot : ¬ ξ ≤ η := fun hle => hneq (le_antisymm (hmax η
              (Finsupp.mem_support_iff.mpr hη)) hle)
            simp [hnot]) (by simp)
        _ = x.1.2 ξ := by simp
    have hz := hx (w Λ ξ n)
    rw [alternating_w, hV, zero_add, hsum] at hz
    exact (Finsupp.mem_support_iff.mp hξ) hz
  have hV : x.1.1 = 0 := by
    apply Finsupp.ext
    intro i
    simpa [hU] using hx (w Λ i.1 i.2)
  exact Prod.ext (Prod.ext hV hU) hW

end NonCalkinAlgebra.OrderedCocycle
