import Mathlib

namespace Strat

open MeasureTheory intervalIntegral

theorem unimodal_right (k : ℝ → ℝ) (hk : AntitoneOn k (Set.Ici 0)) {s z y : ℝ}
    (hz : 0 ≤ z) (hs : z / 2 ≤ s) (hy1 : s - z ≤ y) (hy2 : y ≤ s) :
    k |s| ≤ k |y| := by
  have hs0 : 0 ≤ s := by linarith
  have habs : |y| ≤ s := abs_le.mpr ⟨by linarith, hy2⟩
  rw [abs_of_nonneg hs0]
  exact hk (Set.mem_Ici.mpr (abs_nonneg y)) (Set.mem_Ici.mpr hs0) habs

theorem unimodal_left (k : ℝ → ℝ) (hk : AntitoneOn k (Set.Ici 0)) {s y : ℝ}
    (hs : s ≤ 0) (hy2 : y ≤ s) :
    k |y| ≤ k |s| := by
  have h1 : |s| ≤ |y| := by
    rw [abs_of_nonpos hs, abs_of_nonpos (le_trans hy2 hs)]; linarith
  exact hk (Set.mem_Ici.mpr (abs_nonneg s)) (Set.mem_Ici.mpr (abs_nonneg y)) h1

theorem slope_nonpos (k : ℝ → ℝ) (hk : AntitoneOn k (Set.Ici 0)) {s z : ℝ}
    (hz : 0 ≤ z) (hs : z / 2 ≤ s) :
    ∫ y in (s - z)..s, (k |s| - k |y|) ≤ 0 := by
  have hle : s - z ≤ s := by linarith
  have h : 0 ≤ ∫ y in (s - z)..s, (k |y| - k |s|) :=
    intervalIntegral.integral_nonneg hle (fun y hy => by
      have := unimodal_right k hk hz hs hy.1 hy.2
      linarith)
  have e : (∫ y in (s - z)..s, (k |s| - k |y|)) = -∫ y in (s - z)..s, (k |y| - k |s|) := by
    rw [← intervalIntegral.integral_neg]
    congr 1; ext y; ring
  linarith

theorem slope_nonneg (k : ℝ → ℝ) (hk : AntitoneOn k (Set.Ici 0)) {s z : ℝ}
    (hz : 0 ≤ z) (hs : s ≤ 0) :
    0 ≤ ∫ y in (s - z)..s, (k |s| - k |y|) := by
  have hle : s - z ≤ s := by linarith
  exact intervalIntegral.integral_nonneg hle (fun y hy => by
    have := unimodal_left k hk hs hy.2
    linarith)

end Strat
