import Mathlib

namespace Strat

open MeasureTheory Finset

theorem layer_integral_le {η : Measure ℝ} [IsProbabilityMeasure η] {L : Set ℝ} (hL : η Lᶜ = 0)
    {f : ℝ → ℝ} {g : ℝ} (hf : Integrable f η) (hb : ∀ s ∈ L, f s ≤ g) :
    ∫ s, f s ∂η ≤ g := by
  have hae : ∀ᵐ s ∂η, f s ≤ g := by
    have : L ∈ ae η := mem_ae_iff.mpr hL
    filter_upwards [this] with s hs using hb s hs
  calc ∫ s, f s ∂η ≤ ∫ _s, g ∂η := integral_mono_ae hf (integrable_const g) hae
    _ = g := by simp

theorem deficit_le_S {ι : Type*} [Fintype ι] (n g V : ι → ℝ) (hn : ∀ k, 0 ≤ n k)
    (hV : ∀ k, V k ≤ g k) : ∑ k, n k * V k ≤ ∑ k, n k * g k :=
  Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hV k) (hn k)

theorem near_max {ι : Type*} [Fintype ι] (n : ι → ℝ) (hn : ∀ k, 0 ≤ n k) (f : ι → ℝ → ℝ)
    (L : ι → Set ℝ) (hne : ∀ k, (L k).Nonempty) {c : ℝ}
    (h : c < ∑ k, n k * sSup (f k '' L k)) :
    ∃ s : ι → ℝ, (∀ k, s k ∈ L k) ∧ c < ∑ k, n k * f k (s k) := by
  set S := ∑ k, n k * sSup (f k '' L k)
  set N := ∑ k, n k + 1
  have hN : 0 < N := by
    have : 0 ≤ ∑ k, n k := Finset.sum_nonneg fun k _ => hn k
    linarith
  set δ := (S - c) / N
  have hδ : 0 < δ := div_pos (by linarith) hN
  have hex : ∀ k, ∃ s ∈ L k, sSup (f k '' L k) - δ < f k s := by
    intro k
    have hne' : (f k '' L k).Nonempty := (hne k).image _
    obtain ⟨y, ⟨s, hs, rfl⟩, hy⟩ := exists_lt_of_lt_csSup hne' (by linarith : sSup (f k '' L k) - δ < sSup (f k '' L k))
    exact ⟨s, hs, hy⟩
  choose s hs hlt using hex
  refine ⟨s, hs, ?_⟩
  have h1 : ∑ k, n k * (sSup (f k '' L k) - δ) ≤ ∑ k, n k * f k (s k) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hlt k).le (hn k)
  have h2 : ∑ k, n k * (sSup (f k '' L k) - δ) = S - δ * ∑ k, n k := by
    simp only [mul_sub, Finset.sum_sub_distrib, S, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have h3 : δ * ∑ k, n k < S - c := by
    have : δ * ∑ k, n k < δ * N := mul_lt_mul_of_pos_left (by simp [N]) hδ
    have e : δ * N = S - c := by simp only [δ]; field_simp
    linarith
  linarith

theorem mixture_identity {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (w : ι → β → ℝ) (hw : ∀ k, ∑ j, w k j = 1) (F : ι → β → ℝ) :
    ∑ σ : ι → β, (∏ k, w k (σ k)) * ∑ k, F k (σ k) = ∑ k, ∑ j, w k j * F k j := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have key : ∀ σ : ι → β, (∏ l, w l (σ l)) * F k (σ k)
      = ∏ l, (w l (σ l) * if l = k then F k (σ l) else 1) := by
    intro σ
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k]
    simp
  simp_rw [key]
  rw [← Fintype.prod_sum (fun l j => w l j * if l = k then F k j else 1)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  have hrest : ∏ l ∈ Finset.univ.erase k, ∑ j, w l j * (if l = k then F k j else 1) = 1 := by
    refine Finset.prod_eq_one fun l hl => ?_
    have : l ≠ k := Finset.ne_of_mem_erase hl
    simp [this, hw l]
  rw [hrest, mul_one]
  simp

theorem mixture_weights {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (w : ι → β → ℝ) (hw : ∀ k, ∑ j, w k j = 1) :
    ∑ σ : ι → β, ∏ k, w k (σ k) = 1 := by
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun k _ => hw k

theorem jensen_mixture {α : Type*} (t : Finset α) (p v : α → ℝ) (ψ : ℝ → ℝ) (I : Set ℝ)
    (hψ : ConvexOn ℝ I ψ) (hp : ∀ i ∈ t, 0 ≤ p i) (hsum : ∑ i ∈ t, p i = 1)
    (hv : ∀ i ∈ t, v i ∈ I) :
    ψ (∑ i ∈ t, p i * v i) ≤ ∑ i ∈ t, p i * ψ (v i) := by
  simpa [smul_eq_mul] using hψ.map_sum_le hp hsum hv

theorem mixture_le_max {α : Type*} (t : Finset α) (p T : α → ℝ) (hp : ∀ i ∈ t, 0 ≤ p i)
    (hsum : ∑ i ∈ t, p i = 1) {B : ℝ} (hB : ∀ i ∈ t, T i ≤ B) :
    ∑ i ∈ t, p i * T i ≤ B := by
  calc ∑ i ∈ t, p i * T i ≤ ∑ i ∈ t, p i * B :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (hp i hi)
    _ = B := by rw [← Finset.sum_mul, hsum, one_mul]

theorem shift_identity {ι β : Type*} [Fintype ι] [Fintype β] (n : ι → ℝ) (w : ι → β → ℝ)
    (hw : ∀ k, ∑ j, w k j = 1) (G : ι → β → ℝ) (ε : ℝ) (hn : 0 < ∑ k, n k) :
    ∑ k, n k * ∑ j, w k j * (G k j + ε / ∑ k, n k)
      = ∑ k, n k * ∑ j, w k j * G k j + ε := by
  have : ∀ k, ∑ j, w k j * (G k j + ε / ∑ k, n k) = ∑ j, w k j * G k j + ε / ∑ k, n k := by
    intro k
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw k, one_mul]
  rw [Finset.sum_congr rfl (fun k _ => by rw [this k])]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  field_simp

theorem local_domination {κ z a s : ℝ} (hκ : 0 ≤ κ) (hs : a ≤ s) (hpos : 0 < s) :
    κ * max (z - s) 0 ≤ κ * max (z - max a 0) 0 := by
  apply mul_le_mul_of_nonneg_left _ hκ
  apply max_le_max _ le_rfl
  have : max a 0 ≤ s := max_le hs hpos.le
  linarith

theorem placement_cs {ι : Type*} (t : Finset ι) (c ρ w : ι → ℝ) (hc : ∀ i ∈ t, 0 ≤ c i)
    (hρ : ∀ i ∈ t, 0 < ρ i) (hw : ∀ i ∈ t, 0 ≤ w i) :
    (∑ i ∈ t, Real.sqrt (c i) * w i) ^ 2 ≤ (∑ i ∈ t, c i / ρ i * w i) * ∑ i ∈ t, ρ i * w i := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq t (fun i => Real.sqrt (c i / ρ i * w i))
    (fun i => Real.sqrt (ρ i * w i))
  have e1 : ∀ i ∈ t, Real.sqrt (c i / ρ i * w i) * Real.sqrt (ρ i * w i) = Real.sqrt (c i) * w i := by
    intro i hi
    have hρi := hρ i hi
    rw [← Real.sqrt_mul (by have := hc i hi; have := hw i hi; positivity)]
    have : c i / ρ i * w i * (ρ i * w i) = c i * w i ^ 2 := by field_simp
    rw [this, Real.sqrt_mul (hc i hi), Real.sqrt_sq (hw i hi)]
  have e2 : ∀ i ∈ t, Real.sqrt (c i / ρ i * w i) ^ 2 = c i / ρ i * w i := fun i hi =>
    Real.sq_sqrt (by have := hc i hi; have := hρ i hi; have := hw i hi; positivity)
  have e3 : ∀ i ∈ t, Real.sqrt (ρ i * w i) ^ 2 = ρ i * w i := fun i hi =>
    Real.sq_sqrt (by have := hρ i hi; have := hw i hi; positivity)
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at h
  exact h

theorem placement_optimal {ι : Type*} (t : Finset ι) (c w : ι → ℝ) (hc : ∀ i ∈ t, 0 < c i)
    (Z : ℝ) (hZ : 0 < Z) :
    (∑ i ∈ t, c i / (Real.sqrt (c i) / Z) * w i) * ∑ i ∈ t, Real.sqrt (c i) / Z * w i
      = (∑ i ∈ t, Real.sqrt (c i) * w i) ^ 2 := by
  have e : ∀ i ∈ t, c i / (Real.sqrt (c i) / Z) * w i = Z * (Real.sqrt (c i) * w i) := by
    intro i hi
    have hs : 0 < Real.sqrt (c i) := Real.sqrt_pos.mpr (hc i hi)
    have hcs : c i = Real.sqrt (c i) * Real.sqrt (c i) := (Real.mul_self_sqrt (hc i hi).le).symm
    calc c i / (Real.sqrt (c i) / Z) * w i
        = Real.sqrt (c i) * Real.sqrt (c i) / (Real.sqrt (c i) / Z) * w i := by rw [← hcs]
      _ = Z * (Real.sqrt (c i) * w i) := by field_simp
  have e' : ∀ i ∈ t, Real.sqrt (c i) / Z * w i = Z⁻¹ * (Real.sqrt (c i) * w i) := by
    intro i hi; field_simp
  rw [Finset.sum_congr rfl e, Finset.sum_congr rfl e', ← Finset.mul_sum, ← Finset.mul_sum]
  field_simp

theorem convex_in_data {ι : Type*} [Fintype ι] (ψ : ℝ → ℝ) (hψ : ConvexOn ℝ Set.univ ψ)
    (a : ι → ℝ) : ConvexOn ℝ Set.univ (fun n : ι → ℝ => ψ (∑ k, n k * a k)) := by
  refine ⟨convex_univ, fun x _ y _ p q hp hq hpq => ?_⟩
  have e : ∑ k, (p • x + q • y) k * a k = p • (∑ k, x k * a k) + q • ∑ k, y k * a k := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
  simp only [e]
  exact hψ.2 (Set.mem_univ _) (Set.mem_univ _) hp hq hpq

theorem quadratic_bias {α : Type*} (t : Finset α) (p V : α → ℝ) (f : ℝ → ℝ) (d c m : ℝ)
    (hp : ∀ i ∈ t, 0 ≤ p i) (hsum : ∑ i ∈ t, p i = 1) (hm : ∑ i ∈ t, p i * V i = m)
    (hq : ∀ i ∈ t, f m + d * (V i - m) + c * (V i - m) ^ 2 ≤ f (V i)) :
    c * ∑ i ∈ t, p i * (V i - m) ^ 2 ≤ ∑ i ∈ t, p i * f (V i) - f m := by
  have h1 : ∑ i ∈ t, p i * (f m + d * (V i - m) + c * (V i - m) ^ 2) ≤ ∑ i ∈ t, p i * f (V i) :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hq i hi) (hp i hi)
  have h2 : ∑ i ∈ t, p i * (f m + d * (V i - m) + c * (V i - m) ^ 2)
      = f m + d * (∑ i ∈ t, p i * V i - m) + c * ∑ i ∈ t, p i * (V i - m) ^ 2 := by
    have : ∀ i ∈ t, p i * (f m + d * (V i - m) + c * (V i - m) ^ 2)
        = f m * p i + d * (p i * V i) - d * m * p i + c * (p i * (V i - m) ^ 2) :=
      fun i _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hsum]
    ring
  rw [h2, hm] at h1
  linarith

end Strat
