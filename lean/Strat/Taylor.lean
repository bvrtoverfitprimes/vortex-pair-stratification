import Mathlib

namespace Strat

theorem quadratic_lower {f f' f'' : ℝ → ℝ} {lo hi c : ℝ}
    (hf : ∀ x ∈ Set.Icc lo hi, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc lo hi, HasDerivAt f' (f'' x) x)
    (hc : ∀ x ∈ Set.Icc lo hi, 2 * c ≤ f'' x)
    {m x : ℝ} (hm : m ∈ Set.Icc lo hi) (hx : x ∈ Set.Icc lo hi) :
    f m + f' m * (x - m) + c * (x - m) ^ 2 ≤ f x := by
  set h : ℝ → ℝ := fun y => f' y - f' m - 2 * c * (y - m)
  set g : ℝ → ℝ := fun y => f y - f m - f' m * (y - m) - c * (y - m) ^ 2
  have hI : Convex ℝ (Set.Icc lo hi) := convex_Icc lo hi
  have hder_h : ∀ y ∈ Set.Icc lo hi, HasDerivAt h (f'' y - 2 * c) y := by
    intro y hy
    have h1 := (hf' y hy).sub_const (f' m)
    have h2 : HasDerivAt (fun y => 2 * c * (y - m)) (2 * c) y := by
      simpa using ((hasDerivAt_id y).sub_const m).const_mul (2 * c)
    exact h1.sub h2
  have hder_g : ∀ y ∈ Set.Icc lo hi, HasDerivAt g (h y) y := by
    intro y hy
    have h1 := (hf y hy).sub_const (f m)
    have h2 : HasDerivAt (fun y => f' m * (y - m)) (f' m) y := by
      simpa using ((hasDerivAt_id y).sub_const m).const_mul (f' m)
    have h3 : HasDerivAt (fun y => c * (y - m) ^ 2) (2 * c * (y - m)) y := by
      have := (((hasDerivAt_id' y).sub_const m).pow 2).const_mul c
      convert this using 1
      simp
      ring
    convert (h1.sub h2).sub h3 using 1
  have hmono_h : MonotoneOn h (Set.Icc lo hi) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg hI
    · exact fun y hy => (hder_h y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hder_h y (interior_subset hy)).hasDerivWithinAt
    · intro y hy
      have := hc y (interior_subset hy)
      linarith
  have hhm : h m = 0 := by simp [h]
  have hgm : g m = 0 := by simp [g]
  have key : 0 ≤ g x := by
    rcases le_total m x with hmx | hxm
    · have hsub : Set.Icc m x ⊆ Set.Icc lo hi := Set.Icc_subset_Icc hm.1 hx.2
      have : MonotoneOn g (Set.Icc m x) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc m x)
        · exact fun y hy => (hder_g y (hsub hy)).continuousAt.continuousWithinAt
        · intro y hy
          exact (hder_g y (hsub (interior_subset hy))).hasDerivWithinAt
        · intro y hy
          have hy' := interior_subset hy
          have := hmono_h hm (hsub hy') hy'.1
          linarith
      have := this ⟨le_rfl, hmx⟩ ⟨hmx, le_rfl⟩ hmx
      linarith
    · have hsub : Set.Icc x m ⊆ Set.Icc lo hi := Set.Icc_subset_Icc hx.1 hm.2
      have : AntitoneOn g (Set.Icc x m) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x m)
        · exact fun y hy => (hder_g y (hsub hy)).continuousAt.continuousWithinAt
        · intro y hy
          exact (hder_g y (hsub (interior_subset hy))).hasDerivWithinAt
        · intro y hy
          have hy' := interior_subset hy
          have := hmono_h (hsub hy') hm hy'.2
          linarith
      have := this ⟨le_rfl, hxm⟩ ⟨hxm, le_rfl⟩ hxm
      linarith
  simp only [g] at key
  linarith

end Strat
