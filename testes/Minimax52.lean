import Formalizacao.MinimaxFinal

/-!
Instanciações dos dois lados do Teorema 5.2.
Executar em `lean4/formalizacao` com `lake env lean ../../testes/Minimax52.lean`.
-/

open scoped ENNReal
open FormalizacaoMinimax

private def rate (p s : ℝ) (q : ℝ≥0∞) (heightExponent : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N H : ℕ, 2 ≤ N → 2 ≤ H →
    ENNReal.ofReal (c * ((N : ℝ) ^ (-s) + (H : ℝ) ^ heightExponent)) ≤ Dfun p s q N H ∧
    Dfun p s q N H ≤ ENNReal.ofReal (C * ((N : ℝ) ^ (-s) + (H : ℝ) ^ heightExponent))

private def atHalfAndInfinity (p s heightExponent : ℝ) : Prop :=
  rate p s (1 / 2) heightExponent ∧ rate p s ⊤ heightExponent

private theorem rate_at_half_and_infinity {p s heightExponent : ℝ}
    (hp : 1 ≤ p) (hs0 : 0 < s) (hs2 : s < 2)
    (hExponent : -s / aPS p s = heightExponent) : atHalfAndInfinity p s heightExponent := by
  have hhalf : (0 : ℝ≥0∞) < 1 / 2 := ENNReal.div_pos (by simp) (by simp)
  have hinfty : (0 : ℝ≥0∞) < ⊤ := ENNReal.zero_lt_top
  exact ⟨by simpa only [rate, hExponent] using minimax_nh p s (1 / 2) hp hs0 hs2 hhalf,
    by simpa only [rate, hExponent] using minimax_nh p s ⊤ hp hs0 hs2 hinfty⟩

-- Abaixo de 1/p, a altura contribui com H^(-1/5).
example : atHalfAndInfinity 2 (1 / 4) (-1 / 5) :=
  rate_at_half_and_infinity (by norm_num) (by norm_num) (by norm_num) (by norm_num [aPS])

-- Entre 1/p e 1, incluindo s = 1, o expoente da altura é -s.
example : atHalfAndInfinity 2 (3 / 4) (-3 / 4) :=
  rate_at_half_and_infinity (by norm_num) (by norm_num) (by norm_num) (by norm_num [aPS])

example : atHalfAndInfinity 2 1 (-1) :=
  rate_at_half_and_infinity (by norm_num) (by norm_num) (by norm_num) (by norm_num [aPS])

-- Acima de 1, o piso aritmético determina H^(-1).
example : atHalfAndInfinity 2 (3 / 2) (-1) :=
  rate_at_half_and_infinity (by norm_num) (by norm_num) (by norm_num) (by norm_num [aPS])

-- Os dois pontos críticos têm altura linear.
example : atHalfAndInfinity 2 (1 / 2) (-1 / 2) :=
  rate_at_half_and_infinity (by norm_num) (by norm_num) (by norm_num) (by norm_num [aPS])

example : atHalfAndInfinity 1 1 (-1) :=
  rate_at_half_and_infinity (by norm_num) (by norm_num) (by norm_num) (by norm_num [aPS])

example : ∃ r : ℕ, 1 ≤ r ∧ (2 : ℝ) / 2 < (2 : ℝ) ^ r ∧ (2 : ℝ) ^ r ≤ 2 :=
  exists_dyadic_scale le_rfl

example : FormalizacaoLp.classNH 2 4 ⊆ FormalizacaoLp.classNH 3 5 :=
  classNH_mono (by decide) (by decide)
