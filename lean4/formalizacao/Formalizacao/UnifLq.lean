import Formalizacao.LqLemmas

/-!
# Seção 6, parte 1: versões quantitativas dos lemas de `ℓ^q`

Os lemas de `LqLemmas` só concluem finitude. Para as cotas uniformes da Seção 6 é preciso
a dependência explícita:

* `lq_const_mul_le`: `‖c a‖ ≤ c ‖a‖`;
* `lq_add_le`: `‖a + b‖ ≤ K_q (‖a‖ + ‖b‖)`, com `K_q = 2 · 2^{1/q}`;
* `lqNorm_zero`: a sequência nula tem norma nula.
-/

open scoped ENNReal

namespace FormalizacaoLq

open FormalizacaoLp

theorem lq_const_mul_le {q : ℝ≥0∞} (hq : 0 < q) (c : ℝ≥0∞) (a : ℕ → ℝ≥0∞) :
    lqNorm q (fun k => c * a k) ≤ c * lqNorm q a := by
  unfold lqNorm
  split_ifs with hqt
  · exact iSup_le fun k => mul_le_mul_left' (le_iSup a k) c
  · have hp : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
    have hS : ∑' k, (c * a k) ^ q.toReal = c ^ q.toReal * ∑' k, a k ^ q.toReal := by
      rw [← ENNReal.tsum_mul_left]
      congr 1
      funext k
      exact ENNReal.mul_rpow_of_nonneg _ _ hp.le
    rw [hS, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hp.le), ← ENNReal.rpow_mul,
      mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]

theorem lq_add_le {q : ℝ≥0∞} (hq : 0 < q) (a b : ℕ → ℝ≥0∞) :
    lqNorm q (fun k => a k + b k) ≤
      (2 * (2 : ℝ≥0∞) ^ (q.toReal)⁻¹) * (lqNorm q a + lqNorm q b) := by
  by_cases hqt : q = ⊤
  · subst hqt
    simp only [lqNorm, if_pos rfl]
    have h1 : (⨆ k, (a k + b k)) ≤ (⨆ k, a k) + ⨆ k, b k :=
      iSup_le fun k => add_le_add (le_iSup a k) (le_iSup b k)
    calc (⨆ k, (a k + b k)) ≤ (⨆ k, a k) + ⨆ k, b k := h1
      _ ≤ (2 * (2 : ℝ≥0∞) ^ (ENNReal.toReal ⊤)⁻¹) * ((⨆ k, a k) + ⨆ k, b k) := by
          simp only [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, mul_one]
          exact le_mul_of_one_le_left (zero_le _) (by norm_num)
  · have hp : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
    have hinv : 0 < (q.toReal)⁻¹ := inv_pos.2 hp
    simp only [lqNorm, if_neg hqt]
    set A := ∑' k, a k ^ q.toReal with hA
    set B := ∑' k, b k ^ q.toReal with hB
    have hS : ∑' k, (a k + b k) ^ q.toReal ≤ (2 : ℝ≥0∞) ^ q.toReal * (A + B) := by
      calc ∑' k, (a k + b k) ^ q.toReal
          ≤ ∑' k, (2 : ℝ≥0∞) ^ q.toReal * (a k ^ q.toReal + b k ^ q.toReal) :=
            ENNReal.tsum_le_tsum fun k => add_rpow_le_two_rpow _ _ hp
        _ = (2 : ℝ≥0∞) ^ q.toReal * (A + B) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
    calc (∑' k, (a k + b k) ^ q.toReal) ^ (q.toReal)⁻¹
        ≤ ((2 : ℝ≥0∞) ^ q.toReal * (A + B)) ^ (q.toReal)⁻¹ :=
          ENNReal.rpow_le_rpow hS hinv.le
      _ = 2 * (A + B) ^ (q.toReal)⁻¹ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hinv.le, ← ENNReal.rpow_mul,
            mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]
      _ ≤ 2 * ((2 : ℝ≥0∞) ^ (q.toReal)⁻¹ * (A ^ (q.toReal)⁻¹ + B ^ (q.toReal)⁻¹)) :=
          mul_le_mul_left' (add_rpow_le_two_rpow _ _ hinv) _
      _ = (2 * (2 : ℝ≥0∞) ^ (q.toReal)⁻¹) * (A ^ (q.toReal)⁻¹ + B ^ (q.toReal)⁻¹) := by ring

theorem lqNorm_zero {q : ℝ≥0∞} (hq : 0 < q) : lqNorm q (fun _ : ℕ => (0 : ℝ≥0∞)) = 0 := by
  unfold lqNorm
  split_ifs with hqt
  · simp
  · have hp : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
    simp [ENNReal.zero_rpow_of_pos hp, ENNReal.zero_rpow_of_pos (inv_pos.2 hp)]

end FormalizacaoLq
