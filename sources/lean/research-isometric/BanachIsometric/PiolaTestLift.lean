import BanachIsometric.PiolaIdentity

/-! # Lifting a spatial test function to the homotopy cylinder -/

namespace BanachIsometric

noncomputable def piolaInitLinear (n : ℕ) : PiolaSpace (n + 1) →L[ℝ] PiolaSpace n :=
  ContinuousLinearMap.pi (fun i : Fin n => ContinuousLinearMap.proj i.castSucc)

@[simp] theorem piolaInitLinear_apply {n : ℕ} (x : PiolaSpace (n + 1)) :
    piolaInitLinear n x = Fin.init x := rfl

def piolaLiftTest {n : ℕ} (ψ : PiolaSpace n → ℝ) (z : PiolaSpace (n + 1)) : ℝ :=
  ψ (Fin.init z)

theorem contDiff_piolaLiftTest {n : ℕ} {ψ : PiolaSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) : ContDiff ℝ 1 (piolaLiftTest ψ) := by
  exact hψ.comp (piolaInitLinear n).contDiff

@[simp] theorem piolaLiftTest_snoc {n : ℕ} (ψ : PiolaSpace n → ℝ)
    (x : PiolaSpace n) (t : ℝ) : piolaLiftTest ψ (Fin.snoc x t) = ψ x := by
  simp only [piolaLiftTest, Fin.init_snoc]

end BanachIsometric
