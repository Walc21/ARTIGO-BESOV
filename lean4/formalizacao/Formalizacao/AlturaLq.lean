import Formalizacao.LqLemmas

/-!
# Auxiliares de `ℓ^q` para a altura crítica (auditoria, Parte V)

Homogeneidade `ℓ^q(c·a) = c·ℓ^q(a)`, a desigualdade `ℓ^q(a+b) ≤ 2((ℓ^q a)^Q + (ℓ^q b)^Q)^{1/Q}`
com `Q = q.toReal`, e uma majorante geométrica para `(r+2)ρ^r`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace FormalizacaoLqAux

open FormalizacaoLq FormalizacaoLp

/-- Homogeneidade de `ℓ^q` por constante finita. -/
lemma lqNorm_const_mul {q : ℝ≥0∞} (hq : 0 < q) {c : ℝ≥0∞} (hc : c ≠ ⊤) (a : ℕ → ℝ≥0∞) :
    lqNorm q (fun r => c * a r) = c * lqNorm q a := by
  unfold lqNorm
  split_ifs with hqt
  · rw [ENNReal.mul_iSup]
  · have hQ : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
    have hsum : ∀ r, (c * a r) ^ q.toReal = c ^ q.toReal * a r ^ q.toReal :=
      fun r => ENNReal.mul_rpow_of_nonneg _ _ hQ.le
    simp only [hsum]
    rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hQ.le),
      ← ENNReal.rpow_mul, mul_inv_cancel₀ hQ.ne', ENNReal.rpow_one]

/-- Potência do `ℓ^q` de uma sequência: `(ℓ^q a)^Q = Σ a^Q`. -/
lemma lqNorm_rpow_eq {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤) (a : ℕ → ℝ≥0∞) :
    (lqNorm q a) ^ q.toReal = ∑' r, a r ^ q.toReal := by
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
  unfold lqNorm
  rw [if_neg hqt, ← ENNReal.rpow_mul, inv_mul_cancel₀ hQ.ne', ENNReal.rpow_one]

/-- `ℓ^q(a+b) ≤ 2((ℓ^q a)^Q + (ℓ^q b)^Q)^{1/Q}`. -/
lemma lqNorm_add_le {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤) (a b : ℕ → ℝ≥0∞) :
    lqNorm q (fun r => a r + b r) ≤
      2 * ((lqNorm q a) ^ q.toReal + (lqNorm q b) ^ q.toReal) ^ q.toReal⁻¹ := by
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
  have hbound : ∑' r, (a r + b r) ^ q.toReal ≤
      (2 : ℝ≥0∞) ^ q.toReal * ((lqNorm q a) ^ q.toReal + (lqNorm q b) ^ q.toReal) := by
    rw [lqNorm_rpow_eq hq hqt a, lqNorm_rpow_eq hq hqt b, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro r
    exact add_rpow_le_two_rpow (a r) (b r) hQ
  unfold lqNorm
  rw [if_neg hqt]
  calc (∑' r, (a r + b r) ^ q.toReal) ^ q.toReal⁻¹
      ≤ ((2 : ℝ≥0∞) ^ q.toReal * ((lqNorm q a) ^ q.toReal + (lqNorm q b) ^ q.toReal)) ^
          q.toReal⁻¹ := ENNReal.rpow_le_rpow hbound (inv_nonneg.mpr hQ.le)
    _ = 2 * ((lqNorm q a) ^ q.toReal + (lqNorm q b) ^ q.toReal) ^ q.toReal⁻¹ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hQ.le), ← ENNReal.rpow_mul,
          mul_inv_cancel₀ hQ.ne', ENNReal.rpow_one]

/-- Majorante geométrica de `(r+2) ρ^r`: existe `K'` com `(r+2)ρ^r ≤ K' σ^r` para `ρ < σ`. -/
lemma poly_geom_majorant {ρ σ : ℝ} (hρ : 0 < ρ) (hρσ : ρ < σ) :
    ∃ K' : ℝ, 0 < K' ∧ ∀ r : ℕ, ((r : ℝ) + 2) * ρ ^ r ≤ K' * σ ^ r := by
  set θ : ℝ := σ / ρ with hθ
  have hθ1 : 1 < θ := by rw [hθ, one_lt_div hρ]; exact hρσ
  have hθpos : 0 < θ - 1 := by linarith
  refine ⟨1 / (θ - 1) + 2, by positivity, fun r => ?_⟩
  have hbern : 1 + (r : ℝ) * (θ - 1) ≤ θ ^ r := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ θ - 1 by linarith) r
    simpa [add_sub_cancel] using this
  have hθr : 0 ≤ θ ^ r := by positivity
  have hρr : ρ ^ r * θ ^ r = σ ^ r := by
    rw [← mul_pow, hθ]; congr 1; field_simp
  have hr_le : (r : ℝ) ≤ θ ^ r / (θ - 1) := by
    rw [le_div_iff₀ hθpos]; nlinarith [hbern]
  have hpos : 0 ≤ ρ ^ r := by positivity
  calc ((r : ℝ) + 2) * ρ ^ r ≤ (θ ^ r / (θ - 1) + 2 * θ ^ r) * ρ ^ r := by
        apply mul_le_mul_of_nonneg_right _ hpos
        nlinarith [hr_le, hθr]
    _ = (1 / (θ - 1) + 2) * σ ^ r := by
        rw [← hρr]; field_simp

end FormalizacaoLqAux
