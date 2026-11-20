import Formalizacao.Whitney5

/-!
# Whitney em `L^p` (M5), parte 6: a parte interior

Em `J = [a, a+8δ]`, `I = [a+δ, a+7δ]`, `c = a+4δ`: `ft = f` em `J`, logo as segundas diferenças
centradas em pontos de `I` de passo `≤ δ` só usam valores de `f` em `J`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace FormalizacaoW

variable {a : ℝ} {f : ℝ → ℝ}

lemma ft_eq_of_mem {a b : ℝ} {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc a b) : ft a b f x = f x := by
  unfold ft; exact Set.indicator_of_mem hx _

/-- para `x ∈ I`, `|w| ≤ δ`: `W` de `ft` coincide com `W` de `f` -/
lemma Wt_ft_eq {δ : ℝ} {x w : ℝ} (hx : x ∈ Icc (a + δ) (a + 7 * δ)) (hw : |w| ≤ δ) :
    Wt (ft a (a + 8 * δ) f) x w = Wt f x w := by
  have h1 := abs_le.1 hw
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) hw
  unfold Wt
  rw [ft_eq_of_mem (a := a) (b := a + 8 * δ) (x := x + w) ⟨by linarith [hx.1], by linarith [hx.2]⟩,
    ft_eq_of_mem (a := a) (b := a + 8 * δ) (x := x - w) ⟨by linarith [hx.1], by linarith [hx.2]⟩,
    ft_eq_of_mem (a := a) (b := a + 8 * δ) (x := x) ⟨by linarith [hx.1], by linarith [hx.2]⟩]

lemma Gs_eq {δ : ℝ} (hδ : 0 < δ) {r : ℝ} (hr : r ∈ Icc (a + δ) (a + 7 * δ)) :
    Gs a (a + 8 * δ) f δ r = Wt f r δ / δ ^ 2 := by
  have := Wt_ft_eq (f := f) hr (by rw [abs_of_pos hδ])
  unfold Gs
  rw [← this]; unfold Wt; ring

lemma rpow_arith_6 {δ p : ℝ} (hδ : 0 < δ) :
    (6 * δ) ^ (2 * p) * (1 / δ ^ 2) ^ p = (6 : ℝ) ^ (2 * p) := by
  have h1 : (6 * δ) ^ (2 * p) = (6 : ℝ) ^ (2 * p) * δ ^ (2 * p) :=
    Real.mul_rpow (by norm_num) hδ.le
  have h2 : (δ ^ 2) ^ p = δ ^ (2 * p) := by
    rw [← Real.rpow_natCast δ 2, ← Real.rpow_mul hδ.le]; norm_num
  have h3 : (1 / δ ^ 2) ^ p = 1 / δ ^ (2 * p) := by
    rw [Real.div_rpow zero_le_one (by positivity), Real.one_rpow, h2]
  have h4 : δ ^ (2 * p) ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
  rw [h1, h3]
  field_simp

lemma enorm_rpow_scale {c : ℝ} (hc : 0 < c) (x p : ℝ) (hp : 0 ≤ p) :
    ‖c * x‖ₑ ^ p = ENNReal.ofReal (c ^ p) * ‖x‖ₑ ^ p := by
  rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hp, Real.enorm_eq_ofReal_abs, abs_of_pos hc,
    ENNReal.ofReal_rpow_of_nonneg hc.le hp]

/-- **A parte de Taylor em termos de `W`:**
`∫_I |g - A|^p ≤ 6^{2p} ∫_I |W(·; δ)|^p`. -/
theorem taylor_W {δ : ℝ} {p : ℝ} (hp : 1 ≤ p) (hf : IntegrableOn f (Icc a (a + 8 * δ)))
    (hδ : 0 < δ) :
    ∫⁻ x in Icc (a + δ) (a + 7 * δ),
        ‖gs a (a + 8 * δ) f δ x - (gs a (a + 8 * δ) f δ (a + 4 * δ) +
          gs' a (a + 8 * δ) f δ (a + 4 * δ) * (x - (a + 4 * δ)))‖ₑ ^ p ≤
      ENNReal.ofReal (6 ^ (2 * p)) * ∫⁻ x in Icc (a + δ) (a + 7 * δ), ‖Wt f x δ‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have ht := taylor_lp hp hf δ (lo := a + δ) (hi := a + 7 * δ) (c := a + 4 * δ)
    (by linarith) ⟨by linarith, by linarith⟩
  refine ht.trans ?_
  have hlen : a + 7 * δ - (a + δ) = 6 * δ := by ring
  rw [hlen]
  have hc : 0 < 1 / δ ^ 2 := by positivity
  have hG : ∫⁻ r in Icc (a + δ) (a + 7 * δ), ‖Gs a (a + 8 * δ) f δ r‖ₑ ^ p =
      ENNReal.ofReal ((1 / δ ^ 2) ^ p) * ∫⁻ r in Icc (a + δ) (a + 7 * δ), ‖Wt f r δ‖ₑ ^ p := by
    have : ∫⁻ r in Icc (a + δ) (a + 7 * δ), ‖Gs a (a + 8 * δ) f δ r‖ₑ ^ p =
        ∫⁻ r in Icc (a + δ) (a + 7 * δ), ENNReal.ofReal ((1 / δ ^ 2) ^ p) * ‖Wt f r δ‖ₑ ^ p := by
      refine setLIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
      rw [Gs_eq hδ hr, show Wt f r δ / δ ^ 2 = (1 / δ ^ 2) * Wt f r δ by ring]
      exact enorm_rpow_scale hc _ p hp0.le
    rw [this, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h6 : 0 < 6 * δ := by linarith
  rw [hG, ENNReal.ofReal_rpow_of_pos h6, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    rpow_arith_6 hδ]

end FormalizacaoW
