import Mathlib

namespace Strat

open intervalIntegral MeasureTheory

theorem closed_form_shift (K : ℝ → ℝ) (s z : ℝ) :
    ∫ u in (0 : ℝ)..z, u * K (s - z + u) = ∫ y in (s - z)..s, K y * (z - s + y) := by
  have h := intervalIntegral.integral_comp_add_right (fun y => K y * (z - s + y)) (s - z)
    (a := (0 : ℝ)) (b := z)
  simp only [zero_add] at h
  have e : z + (s - z) = s := by ring
  rw [e] at h
  rw [← h]
  congr 1
  ext u
  ring_nf

theorem third_integral (s z : ℝ) :
    ∫ y in (s - z)..s, (s ^ 2 - y ^ 2) = s * z ^ 2 - z ^ 3 / 3 := by
  have h : ∀ y ∈ Set.uIcc (s - z) s,
      HasDerivAt (fun y : ℝ => s ^ 2 * y - y ^ 3 / 3) (s ^ 2 - y ^ 2) y := by
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => s ^ 2 * y) (s ^ 2) y := by
      simpa using (hasDerivAt_id y).const_mul (s ^ 2)
    have h2 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (y ^ 2) y := by
      have := (hasDerivAt_pow 3 y).div_const 3
      convert this using 1
      norm_num
    exact h1.sub h2
  have hint : IntervalIntegrable (fun y : ℝ => s ^ 2 - y ^ 2) volume (s - z) s :=
    (continuous_const.sub (continuous_pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h hint]
  ring

theorem third_sign {k2 s z : ℝ} (hk : k2 < 0) (hz : 0 < z) :
    0 < k2 / 2 * (s * z ^ 2 - z ^ 3 / 3) ↔ s < z / 3 := by
  have hz2 : 0 < z ^ 2 := by positivity
  have e : s * z ^ 2 - z ^ 3 / 3 = z ^ 2 * (s - z / 3) := by ring
  rw [e]
  constructor
  · intro h
    rcases lt_or_ge s (z / 3) with hs | hs
    · exact hs
    · have : 0 ≤ z ^ 2 * (s - z / 3) := mul_nonneg hz2.le (by linarith)
      nlinarith
  · intro hs
    have : z ^ 2 * (s - z / 3) < 0 := mul_neg_of_pos_of_neg hz2 (by linarith)
    nlinarith

theorem segment_antideriv {a b γ x : ℝ} (hγ : 0 < γ) (ha : a = γ ^ 2) (hx : 0 < a + b * x) :
    HasDerivAt (fun x => 2 * x / (γ + Real.sqrt (a + b * x))) (1 / Real.sqrt (a + b * x)) x := by
  set r := Real.sqrt (a + b * x) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hx
  have hr2 : r ^ 2 = a + b * x := Real.sq_sqrt hx.le
  have hlin : HasDerivAt (fun x => a + b * x) b x := by
    simpa using ((hasDerivAt_id x).const_mul b).const_add a
  have hsq : HasDerivAt (fun x => Real.sqrt (a + b * x)) (b / (2 * r)) x := by
    have := hlin.sqrt hx.ne'
    simpa [hr, div_eq_mul_inv, mul_comm] using this
  have hden : HasDerivAt (fun x => γ + Real.sqrt (a + b * x)) (b / (2 * r)) x := by
    simpa using hsq.const_add γ
  have hnum : HasDerivAt (fun x => 2 * x) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have hne : γ + r ≠ 0 := by linarith
  have h := hnum.div hden hne
  convert h using 1
  field_simp
  nlinarith [hr2, ha]

theorem segment_integral {γ₀ γ₁ d : ℝ} (h₀ : 0 < γ₀) (h₁ : 0 < γ₁) (hd : 0 < d) :
    ∫ x in (0 : ℝ)..d, 1 / Real.sqrt (γ₀ ^ 2 + (γ₁ ^ 2 - γ₀ ^ 2) / d * x)
      = 2 * d / (γ₀ + γ₁) := by
  set b := (γ₁ ^ 2 - γ₀ ^ 2) / d
  have hpos : ∀ x ∈ Set.uIcc 0 d, 0 < γ₀ ^ 2 + b * x := by
    intro x hx
    rw [Set.uIcc_of_le hd.le] at hx
    have e : γ₀ ^ 2 + b * x = γ₀ ^ 2 * (1 - x / d) + γ₁ ^ 2 * (x / d) := by
      simp only [b]; field_simp; ring
    rw [e]
    have h1 : 0 ≤ x / d := div_nonneg hx.1 hd.le
    have h2 : x / d ≤ 1 := (div_le_one hd).mpr hx.2
    rcases eq_or_lt_of_le h2 with h | h
    · rw [h]; nlinarith [sq_pos_of_pos h₁]
    · nlinarith [sq_pos_of_pos h₀, sq_pos_of_pos h₁]
  have hderiv : ∀ x ∈ Set.uIcc 0 d, HasDerivAt (fun x => 2 * x / (γ₀ + Real.sqrt (γ₀ ^ 2 + b * x)))
      (1 / Real.sqrt (γ₀ ^ 2 + b * x)) x :=
    fun x hx => segment_antideriv h₀ rfl (hpos x hx)
  have hcont : ContinuousOn (fun x => 1 / Real.sqrt (γ₀ ^ 2 + b * x)) (Set.uIcc 0 d) := by
    apply ContinuousOn.div continuousOn_const
    · exact (continuous_const.add (continuous_const.mul continuous_id)).sqrt.continuousOn
    · intro x hx; exact (Real.sqrt_pos.mpr (hpos x hx)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have e : γ₀ ^ 2 + b * d = γ₁ ^ 2 := by simp only [b]; field_simp; ring
  rw [e, Real.sqrt_sq h₁.le]
  simp

noncomputable def psi (v : ℝ) : ℝ := (1 - 2 * v) ^ (-(1 : ℝ) / 2)

theorem psi_deriv {v : ℝ} (hv : v < 1 / 2) :
    HasDerivAt psi ((1 - 2 * v) ^ (-(3 : ℝ) / 2)) v := by
  have hpos : 0 < 1 - 2 * v := by linarith
  have hlin : HasDerivAt (fun v : ℝ => 1 - 2 * v) (-2) v := by
    simpa using ((hasDerivAt_id v).const_mul 2).const_sub 1
  have h := hlin.rpow_const (p := -(1 : ℝ) / 2) (Or.inl hpos.ne')
  unfold psi
  convert h using 1
  have e : -(1 : ℝ) / 2 - 1 = -(3 : ℝ) / 2 := by norm_num
  rw [e]
  ring

theorem psi_deriv2 {v : ℝ} (hv : v < 1 / 2) :
    HasDerivAt (fun v : ℝ => (1 - 2 * v) ^ (-(3 : ℝ) / 2)) (3 * (1 - 2 * v) ^ (-(5 : ℝ) / 2)) v := by
  have hpos : 0 < 1 - 2 * v := by linarith
  have hlin : HasDerivAt (fun v : ℝ => 1 - 2 * v) (-2) v := by
    simpa using ((hasDerivAt_id v).const_mul 2).const_sub 1
  have h := hlin.rpow_const (p := -(3 : ℝ) / 2) (Or.inl hpos.ne')
  convert h using 1
  have e : -(3 : ℝ) / 2 - 1 = -(5 : ℝ) / 2 := by norm_num
  rw [e]
  ring

theorem psi_deriv2_mono {u v : ℝ} (huv : u ≤ v) (hv : v < 1 / 2) :
    3 * (1 - 2 * u) ^ (-(5 : ℝ) / 2) ≤ 3 * (1 - 2 * v) ^ (-(5 : ℝ) / 2) := by
  have h1 : 0 < 1 - 2 * v := by linarith
  have h2 : 1 - 2 * v ≤ 1 - 2 * u := by linarith
  have := Real.rpow_le_rpow_of_nonpos h1 h2 (by norm_num : (-(5 : ℝ) / 2) ≤ 0)
  linarith

end Strat
