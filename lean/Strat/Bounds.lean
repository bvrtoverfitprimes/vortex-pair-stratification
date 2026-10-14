import Mathlib

namespace Strat

open MeasureTheory ProbabilityTheory Filter Topology

theorem crossover {m c v : ℝ} (hm : 0 < m) (hmc : m < c) (hv : 0 ≤ v) :
    v / (v + (c - m) ^ 2) ≤ m / c ↔ v ≤ m * (c - m) := by
  have hc : 0 < c := by linarith
  have hd : 0 < v + (c - m) ^ 2 := by nlinarith [sq_pos_of_pos (sub_pos.mpr hmc)]
  rw [div_le_div_iff₀ hd hc]
  constructor <;> intro h <;> nlinarith [sub_pos.mpr hmc]

theorem crossover_eq {m c : ℝ} (hm : 0 < m) (hmc : m < c) :
    m * (c - m) / (m * (c - m) + (c - m) ^ 2) = m / c := by
  have h1 : 0 < c - m := sub_pos.mpr hmc
  have hc : 0 < c := by linarith
  rw [div_eq_div_iff (by positivity) hc.ne']
  ring

theorem two_point_mean {m c v : ℝ} (hmc : m < c) (hv : 0 ≤ v) :
    let a := c - m
    let p := v / (v + a ^ 2)
    p * c + (1 - p) * (m - v / a) = m := by
  intro a p
  have ha : 0 < a := sub_pos.mpr hmc
  have hd : 0 < v + a ^ 2 := by positivity
  simp only [p]
  field_simp
  simp only [a]
  ring

theorem two_point_var {m c v : ℝ} (hmc : m < c) (hv : 0 ≤ v) :
    let a := c - m
    let p := v / (v + a ^ 2)
    p * (c - m) ^ 2 + (1 - p) * (v / a) ^ 2 = v := by
  intro a p
  have ha : 0 < a := sub_pos.mpr hmc
  have hd : 0 < v + a ^ 2 := by positivity
  simp only [p]
  field_simp
  simp only [a]
  ring

theorem two_point_lower_nonneg {m c v : ℝ} (hmc : m < c) (hv : v ≤ m * (c - m)) :
    0 ≤ m - v / (c - m) := by
  have ha : 0 < c - m := sub_pos.mpr hmc
  rw [sub_nonneg, div_le_iff₀ ha]
  linarith

theorem markov_case_moments {m c v ε A : ℝ} (hc : 0 < c) (hA : c < A)
    (hε : ε * c * (A - c) = v - m * (c - m)) :
    let q := ε * c / A
    (m / c - ε) * c + q * A = m ∧ (m / c - ε) * c ^ 2 + q * A ^ 2 - m ^ 2 = v := by
  intro q
  have hA0 : 0 < A := by linarith
  simp only [q]
  constructor
  · field_simp; ring
  · field_simp
    nlinarith [hε]

theorem markov_case_limit {m c v : ℝ} (hc : 0 < c) :
    Tendsto (fun A : ℝ => m / c - (v - m * (c - m)) / (c * (A - c))
      + (v - m * (c - m)) / (c * (A - c)) * c / A) atTop (𝓝 (m / c)) := by
  have h1 : Tendsto (fun A : ℝ => (v - m * (c - m)) / (c * (A - c))) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := v - m * (c - m))).div_atTop
      ((tendsto_atTop_add_const_right atTop (-c) tendsto_id).const_mul_atTop hc)
    refine this.congr (fun A => ?_)
    simp [sub_eq_add_neg]
  have h2 : Tendsto (fun A : ℝ => c / A) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have := (tendsto_const_nhds (x := m / c)).sub h1 |>.add (h1.mul h2)
  simpa [mul_div_assoc] using this

theorem markov_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {c : ℝ} (hY : 0 ≤ Y) (hint : Integrable Y P) :
    c * (P {ω | c ≤ Y ω}).toReal ≤ ∫ ω, Y ω ∂P :=
  mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hY) hint c

theorem cantelli {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {a v : ℝ} (ha : 0 < a) (hX : MemLp X 2 P) (hmean : ∫ ω, X ω ∂P = 0)
    (hvar : ∫ ω, X ω ^ 2 ∂P = v) :
    (P {ω | a ≤ X ω}).toReal ≤ v / (v + a ^ 2) := by
  have hv : 0 ≤ v := hvar ▸ integral_nonneg (fun ω => sq_nonneg (X ω))
  set t := v / a with ht
  have ht0 : 0 ≤ t := div_nonneg hv ha.le
  have hXi : Integrable X P := hX.integrable one_le_two
  have hX2 : Integrable (fun ω => X ω ^ 2) P := hX.integrable_sq
  have hf : Integrable (fun ω => (X ω + t) ^ 2) P := by
    have : (fun ω => (X ω + t) ^ 2) = fun ω => X ω ^ 2 + 2 * t * X ω + t ^ 2 := by
      ext ω; ring
    rw [this]
    exact (hX2.add (hXi.const_mul _)).add (integrable_const _)
  have hint : ∫ ω, (X ω + t) ^ 2 ∂P = v + t ^ 2 := by
    have : (fun ω => (X ω + t) ^ 2) = fun ω => X ω ^ 2 + 2 * t * X ω + t ^ 2 := by
      ext ω; ring
    have e1 : ∫ ω, (X ω ^ 2 + 2 * t * X ω + t ^ 2) ∂P
        = ∫ ω, (X ω ^ 2 + 2 * t * X ω) ∂P + ∫ _ω, t ^ 2 ∂P :=
      integral_add (hX2.add (hXi.const_mul _)) (integrable_const _)
    have e2 : ∫ ω, (X ω ^ 2 + 2 * t * X ω) ∂P = ∫ ω, X ω ^ 2 ∂P + ∫ ω, 2 * t * X ω ∂P :=
      integral_add hX2 (hXi.const_mul _)
    rw [this, e1, e2, integral_const_mul, hmean, hvar]
    simp
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun ω => sq_nonneg (X ω + t))) hf ((a + t) ^ 2)
  have hsub : {ω | a ≤ X ω} ⊆ {ω | (a + t) ^ 2 ≤ (X ω + t) ^ 2} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have : 0 ≤ a + t := by linarith
    nlinarith
  have hmono : (P {ω | a ≤ X ω}).toReal ≤ (P {ω | (a + t) ^ 2 ≤ (X ω + t) ^ 2}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hat : 0 < (a + t) ^ 2 := by positivity
  rw [hint, measureReal_def] at hm
  have h3 := mul_le_mul_of_nonneg_right hmono hat.le
  have key : (P {ω | a ≤ X ω}).toReal ≤ (v + t ^ 2) / (a + t) ^ 2 := by
    rw [le_div_iff₀ hat]
    nlinarith [hm, h3]
  have e : (v + t ^ 2) / (a + t) ^ 2 = v / (v + a ^ 2) := by
    have hva : 0 < v + a ^ 2 := by positivity
    rw [ht, div_eq_div_iff (by positivity) hva.ne']
    field_simp
    ring
  linarith [key, e.le, e.ge]

theorem schur_identities {M : Type*} [Fintype M] (S : Matrix M M ℝ)
    (a : M → ℝ) (hv : 0 < a ⬝ᵥ S.mulVec a) :
    let v := a ⬝ᵥ S.mulVec a
    let u := (1 / v) • S.mulVec a
    a ⬝ᵥ u = 1 ∧ a ⬝ᵥ (S.mulVec a) - v * (a ⬝ᵥ u) ^ 2 = 0 := by
  intro v u
  have h1 : a ⬝ᵥ u = 1 := by
    simp only [u, dotProduct_smul, smul_eq_mul]
    exact one_div_mul_cancel hv.ne'
  refine ⟨h1, ?_⟩
  rw [h1]
  show a ⬝ᵥ S.mulVec a - (a ⬝ᵥ S.mulVec a) * 1 ^ 2 = 0
  ring

theorem schur_psd {M : Type*} [Fintype M] (S : Matrix M M ℝ) (hS : S.IsSymm)
    (hpsd : ∀ x : M → ℝ, 0 ≤ x ⬝ᵥ S.mulVec x) (a : M → ℝ) (hv : 0 < a ⬝ᵥ S.mulVec a)
    (x : M → ℝ) :
    (x ⬝ᵥ S.mulVec a) ^ 2 / (a ⬝ᵥ S.mulVec a) ≤ x ⬝ᵥ S.mulVec x := by
  set A := a ⬝ᵥ S.mulVec a
  set B := x ⬝ᵥ S.mulVec a
  set C := x ⬝ᵥ S.mulVec x
  have hsym : a ⬝ᵥ S.mulVec x = B := by
    simp only [B]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS.eq, dotProduct_comm]
  have hq : ∀ τ : ℝ, 0 ≤ A * (τ * τ) + (-2 * B) * τ + C := by
    intro τ
    have h := hpsd (x - τ • a)
    have e : (x - τ • a) ⬝ᵥ S.mulVec (x - τ • a) = A * (τ * τ) + (-2 * B) * τ + C := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [hsym]
      ring
    linarith [e ▸ h]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  rw [div_le_iff₀ hv]
  nlinarith

theorem cantelli_vector_law {M : Type*} [Fintype M] (a nbar u R : M → ℝ) (m Y : ℝ)
    (hm : a ⬝ᵥ nbar = m) (hu : a ⬝ᵥ u = 1) (hR : a ⬝ᵥ R = 0) :
    a ⬝ᵥ (nbar + (Y - m) • u + R) = Y := by
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hm, hu, hR]
  ring

end Strat
