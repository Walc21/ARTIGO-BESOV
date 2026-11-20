import Formalizacao.LowSum
import Formalizacao.Schedules

/-!
# Regimes `s ≤ 1/p`, parte 7: pesos de quantização e expoente `m`

* `lq_geom_all`, `lq_poly_all`: critérios `ℓ^q` (incluindo `q = ∞`).
* `wreal_geom`, `wreal_poly`: cotas reais do peso `2^{(k+1)s}/(2·2^{(k+1)+m})`.
* `mDiag κ r = ⌈κ log₂ r⌉`: `r^κ ≤ 2^{m} ≤ 2 r^κ`, o expoente extra de quantização no caso `s = 1/p`.
-/

open scoped ENNReal
open FormalizacaoLp FormalizacaoLq

namespace FormalizacaoLow

lemma lq_geom_all {q : ℝ≥0∞} (hq : 0 < q) {w : ℕ → ℝ≥0∞} {C ρ : ℝ} (hC : 0 ≤ C)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (h : ∀ k, w k ≤ ENNReal.ofReal (C * ρ ^ k)) :
    lqNorm q w < ⊤ := by
  by_cases hqt : q = ⊤
  · subst hqt
    rw [lqNorm, if_pos rfl]
    refine lt_of_le_of_lt (b := ENNReal.ofReal C) (iSup_le fun k => (h k).trans ?_)
      ENNReal.ofReal_lt_top
    exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hC (pow_le_one₀ hρ0 hρ1.le))
  · exact lq_of_geom_le hq hqt hC hρ0 hρ1 h

lemma lq_poly_all {q : ℝ≥0∞} (hq : 0 < q) {w : ℕ → ℝ≥0∞} {D κ : ℝ} (hD : 0 ≤ D)
    (hκ0 : 0 ≤ κ) (hκ : q ≠ ⊤ → 1 < κ * q.toReal)
    (h : ∀ k, w k ≤ ENNReal.ofReal (D * (((k + 1 : ℕ) : ℝ)) ^ (-κ))) :
    lqNorm q w < ⊤ := by
  by_cases hqt : q = ⊤
  · subst hqt
    rw [lqNorm, if_pos rfl]
    refine lt_of_le_of_lt (b := ENNReal.ofReal D) (iSup_le fun k => (h k).trans ?_)
      ENNReal.ofReal_lt_top
    refine ENNReal.ofReal_le_ofReal ?_
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
    have h1 : ((k + 1 : ℕ) : ℝ) ^ (-κ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hk1 (by linarith)
    exact mul_le_of_le_one_right hD h1
  · exact lq_of_poly_le hq hqt hD (hκ hqt) h

/-- Peso geométrico: `2^{(k+1)s} · 1/(2·2^{(k+1)+e}) ≤ (ρ/2) ρ^k`, `ρ = 2^{s-1}`. -/
lemma wreal_geom (s : ℝ) (k e : ℕ) :
    (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s) * (1 / (2 * 2 ^ ((k + 1) + e))) ≤
      (2 : ℝ) ^ (s - 1) / 2 * ((2 : ℝ) ^ (s - 1)) ^ k := by
  have hρ : 0 < (2 : ℝ) ^ (s - 1) := Real.rpow_pos_of_pos (by norm_num) _
  have h2e : (1 : ℝ) ≤ 2 ^ e := one_le_pow₀ (by norm_num)
  have hx : (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s) =
      (2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (s - 1)) ^ (k + 1) := by
    have := FormalizacaoSched.rpow_two_identity s 1 ((k + 1 : ℕ) : ℝ)
    rw [this, Real.rpow_one, Real.rpow_natCast, Real.rpow_natCast]
  calc (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s) * (1 / (2 * 2 ^ ((k + 1) + e)))
      = ((2 : ℝ) ^ (s - 1)) ^ (k + 1) / (2 * 2 ^ e) := by
        rw [hx, pow_add (2 : ℝ) (k + 1) e]
        field_simp
    _ ≤ ((2 : ℝ) ^ (s - 1)) ^ (k + 1) / 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
        nlinarith
    _ = (2 : ℝ) ^ (s - 1) / 2 * ((2 : ℝ) ^ (s - 1)) ^ k := by
        rw [pow_succ]; ring

/-- Expoente extra de quantização `m = ⌈κ log₂ r⌉`. -/
noncomputable def mDiag (κ : ℝ) (r : ℕ) : ℕ := ⌈κ * Real.logb 2 r⌉₊

lemma rpow_two_logb {r : ℕ} (hr : 1 ≤ r) (κ : ℝ) :
    (2 : ℝ) ^ (κ * Real.logb 2 r) = (r : ℝ) ^ κ := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hr0]

lemma mDiag_ge {κ : ℝ} {r : ℕ} (hr : 1 ≤ r) : (r : ℝ) ^ κ ≤ (2 : ℝ) ^ (mDiag κ r) := by
  have h1 : κ * Real.logb 2 r ≤ (mDiag κ r : ℝ) := Nat.le_ceil _
  calc (r : ℝ) ^ κ = (2 : ℝ) ^ (κ * Real.logb 2 r) := (rpow_two_logb hr κ).symm
    _ ≤ (2 : ℝ) ^ ((mDiag κ r : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = (2 : ℝ) ^ (mDiag κ r) := Real.rpow_natCast _ _

lemma mDiag_le {κ : ℝ} (hκ : 0 ≤ κ) {r : ℕ} (hr : 1 ≤ r) :
    (2 : ℝ) ^ (mDiag κ r) ≤ 2 * (r : ℝ) ^ κ := by
  have hL : 0 ≤ κ * Real.logb 2 r :=
    mul_nonneg hκ (Real.logb_nonneg (by norm_num) (by exact_mod_cast hr))
  have h1 : (mDiag κ r : ℝ) < κ * Real.logb 2 r + 1 := Nat.ceil_lt_add_one hL
  calc (2 : ℝ) ^ (mDiag κ r) = (2 : ℝ) ^ ((mDiag κ r : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2 : ℝ) ^ (κ * Real.logb 2 r + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1.le
    _ = 2 * (r : ℝ) ^ κ := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one, rpow_two_logb hr κ]; ring

/-- Peso polinomial (`s = 1`): se `r^κ ≤ 2^{m r}`, então
`2^{(k+1)·1} · 1/(2·2^{(k+1)+m}) ≤ (1/2)(k+1)^{-κ}`. -/
lemma wreal_poly {κ : ℝ} (m : ℕ → ℕ) (hm : ∀ r : ℕ, 1 ≤ r → (r : ℝ) ^ κ ≤ (2 : ℝ) ^ (m r))
    (k : ℕ) :
    (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * 1) * (1 / (2 * 2 ^ ((k + 1) + m (k + 1)))) ≤
      1 / 2 * (((k + 1 : ℕ) : ℝ)) ^ (-κ) := by
  have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hmk := hm (k + 1) (Nat.le_add_left 1 k)
  have hx : (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * 1) = (2 : ℝ) ^ (k + 1) := by
    rw [mul_one, Real.rpow_natCast]
  have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) ^ κ := Real.rpow_pos_of_pos hk1 _
  rw [hx, pow_add (2 : ℝ) (k + 1) (m (k + 1)), Real.rpow_neg hk1.le]
  have h2m : (0 : ℝ) < 2 ^ (m (k + 1)) := by positivity
  calc (2 : ℝ) ^ (k + 1) * (1 / (2 * (2 ^ (k + 1) * 2 ^ (m (k + 1)))))
      = 1 / (2 * 2 ^ (m (k + 1))) := by field_simp
    _ ≤ 1 / (2 * ((k + 1 : ℕ) : ℝ) ^ κ) := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
    _ = 1 / 2 * (((k + 1 : ℕ) : ℝ) ^ κ)⁻¹ := by field_simp

end FormalizacaoLow
