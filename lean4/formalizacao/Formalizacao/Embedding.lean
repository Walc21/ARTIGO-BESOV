import Formalizacao.Corollary54

/-!
# Núcleo discreto do Lema 5.5 (M6): desigualdade inversa e Bernstein para funções afins

Para uma função afina `v(y) = α + βy` num intervalo `I = [a, a+ℓ]`, o funcional de extremo do
Lema 5.1 reproduz `v` exatamente. Daí:

* `inverse_affine_endpoint`: `|v(e)| ≤ 4 ℓ^{-1/p} ‖v‖_{L^p(I)}` nos dois extremos;
* `inverse_affine_sup`: `sup_I |v| ≤ 8 ℓ^{-1/p} ‖v‖_{L^p(I)}`;
* `bernstein_affine`: `|β| ≤ 8 ℓ^{-1/p-1} ‖v‖_{L^p(I)}`, isto é, `‖v'‖_∞ ≤ C ℓ^{-1} ‖v‖_∞`
  com a mesma `‖v‖_∞` controlada pelo `L^p`.

Não formalizado aqui: a telescopagem `Q_{2^{k+1}} f - Q_{2^k} f`, a cota `‖f - Q_{2^r} f‖_∞`
(que usa a Corolário 5.4 em todas as escalas) e as três regimes da soma (`lp:eq:omega1-regimes`).
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoQuasi

namespace FormalizacaoEmb

/-- `v(x)` é combinação convexa dos extremos: `|v(x)| ≤ |v(a)| + |v(a+ℓ)|` em `[a, a+ℓ]`. -/
theorem abs_affine_le_endpoints {a ℓ α β x : ℝ} (hℓ : 0 < ℓ) (hx : x ∈ Icc a (a + ℓ)) :
    |α + β * x| ≤ |α + β * a| + |α + β * (a + ℓ)| := by
  obtain ⟨h1, h2⟩ := hx
  set t : ℝ := (x - a) / ℓ with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hℓ.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hℓ]; linarith
  have hxe : α + β * x = (1 - t) * (α + β * a) + t * (α + β * (a + ℓ)) := by
    rw [ht]
    field_simp
    ring
  rw [hxe]
  have hA : |(1 - t) * (α + β * a)| ≤ |α + β * a| := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)]
    nlinarith [abs_nonneg (α + β * a)]
  have hB : |t * (α + β * (a + ℓ))| ≤ |α + β * (a + ℓ)| := by
    rw [abs_mul, abs_of_nonneg ht0]
    nlinarith [abs_nonneg (α + β * (a + ℓ))]
  exact (abs_add_le _ _).trans (add_le_add hA hB)

/-- Uma função afina é de `L^p` finita num intervalo limitado. -/
theorem eLpNorm_affine_lt_top {a ℓ α β p : ℝ} (hℓ : 0 < ℓ) (hp : 1 ≤ p) :
    eLpNorm (fun y => α + β * y) (ENNReal.ofReal p) (volume.restrict (Icc a (a + ℓ))) < ⊤ := by
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by linarith)
  refine lt_of_le_of_lt (eLpNorm_le_of_ae_bound (C := |α| + |β| * (|a| + ℓ)) ?_) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    rw [Real.norm_eq_abs]
    have hy' : |y| ≤ |a| + ℓ := by
      rw [abs_le]
      constructor <;> cases abs_cases a <;> linarith [hy.1, hy.2, abs_nonneg a]
    calc |α + β * y| ≤ |α| + |β * y| := abs_add_le _ _
      _ = |α| + |β| * |y| := by rw [abs_mul]
      _ ≤ |α| + |β| * (|a| + ℓ) := by gcongr
  · rw [Measure.restrict_apply_univ, Real.volume_Icc]
    refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ?_ ENNReal.ofReal_ne_top)
      ENNReal.ofReal_lt_top
    rw [hpr]
    have : (0 : ℝ) < p := by linarith
    exact (inv_pos.2 this).le

/-- Desigualdade inversa nos extremos: `|α + βa| ≤ 4 ℓ^{-1/p} ‖v‖_{L^p(I)}`. -/
theorem inverse_affine_left {a ℓ α β p : ℝ} (hℓ : 0 < ℓ) (hp : 1 ≤ p) :
    |α + β * a| ≤ 4 * ℓ ^ (-(1 / p)) *
      (eLpNorm (fun y => α + β * y) (ENNReal.ofReal p) (volume.restrict (Icc a (a + ℓ)))).toReal := by
  have hcont : Continuous fun y : ℝ => α + β * y := by fun_prop
  have hred : α + β * a = ∫ y in Icc a (a + ℓ), kL a ℓ y * (α + β * y) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    exact (integral_kL_mul_affine a ℓ α β hℓ.ne').symm
  rw [hred]
  exact abs_integral_kernel_le hℓ hp (fun y hy => abs_kL_le hℓ hy)
    (by unfold kL; fun_prop) (by fun_prop : Measurable fun y : ℝ => α + β * y).aestronglyMeasurable
    (eLpNorm_affine_lt_top hℓ hp)

/-- Desigualdade inversa no extremo direito: `|α + β(a+ℓ)| ≤ 4 ℓ^{-1/p} ‖v‖_{L^p(I)}`. -/
theorem inverse_affine_right {a ℓ α β p : ℝ} (hℓ : 0 < ℓ) (hp : 1 ≤ p) :
    |α + β * (a + ℓ)| ≤ 4 * ℓ ^ (-(1 / p)) *
      (eLpNorm (fun y => α + β * y) (ENNReal.ofReal p) (volume.restrict (Icc a (a + ℓ)))).toReal := by
  have hcont : Continuous fun y : ℝ => α + β * y := by fun_prop
  have hred : α + β * (a + ℓ) = ∫ y in Icc a (a + ℓ), kR a ℓ y * (α + β * y) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    exact (integral_kR_mul_affine a ℓ α β hℓ.ne').symm
  rw [hred]
  exact abs_integral_kernel_le hℓ hp (fun y hy => abs_kR_le hℓ hy)
    (by unfold kR; fun_prop) (by fun_prop : Measurable fun y : ℝ => α + β * y).aestronglyMeasurable
    (eLpNorm_affine_lt_top hℓ hp)

/-- Desigualdade inversa para afins no intervalo: `sup_I |v| ≤ 8 ℓ^{-1/p} ‖v‖_{L^p(I)}`. -/
theorem inverse_affine_sup {a ℓ α β p : ℝ} (hℓ : 0 < ℓ) (hp : 1 ≤ p) {x : ℝ}
    (hx : x ∈ Icc a (a + ℓ)) :
    |α + β * x| ≤ 8 * ℓ ^ (-(1 / p)) *
      (eLpNorm (fun y => α + β * y) (ENNReal.ofReal p) (volume.restrict (Icc a (a + ℓ)))).toReal := by
  have h1 := abs_affine_le_endpoints (α := α) (β := β) hℓ hx
  have h2 := inverse_affine_left (a := a) (α := α) (β := β) hℓ hp
  have h3 := inverse_affine_right (a := a) (α := α) (β := β) hℓ hp
  linarith

/-- Bernstein para afins: `|β| ≤ 8 ℓ^{-1/p - 1} ‖v‖_{L^p(I)}`. -/
theorem bernstein_affine {a ℓ α β p : ℝ} (hℓ : 0 < ℓ) (hp : 1 ≤ p) :
    |β| ≤ 8 * ℓ ^ (-(1 / p) - 1) *
      (eLpNorm (fun y => α + β * y) (ENNReal.ofReal p) (volume.restrict (Icc a (a + ℓ)))).toReal := by
  have h2 := inverse_affine_left (a := a) (α := α) (β := β) hℓ hp
  have h3 := inverse_affine_right (a := a) (α := α) (β := β) hℓ hp
  have hdiff : β * ℓ = (α + β * (a + ℓ)) - (α + β * a) := by ring
  have hb : |β| * ℓ ≤ |α + β * (a + ℓ)| + |α + β * a| := by
    have : |β * ℓ| ≤ |α + β * (a + ℓ)| + |α + β * a| := by
      rw [hdiff]
      exact (abs_sub _ _).trans (by linarith [abs_sub_comm (α + β * (a + ℓ)) (α + β * a)])
    rwa [abs_mul, abs_of_pos hℓ] at this
  have hrp : ℓ ^ (-(1 / p) - 1) * ℓ = ℓ ^ (-(1 / p)) := by
    rw [Real.rpow_sub hℓ, Real.rpow_one]
    field_simp
  have hpos : 0 < ℓ ^ (-(1 / p) - 1) := Real.rpow_pos_of_pos hℓ _
  have key : |β| * ℓ ≤ ℓ ^ (-(1 / p)) * (8 * (eLpNorm (fun y => α + β * y) (ENNReal.ofReal p)
      (volume.restrict (Icc a (a + ℓ)))).toReal) := by
    have := hb
    nlinarith
  have hfin : |β| ≤ ℓ ^ (-(1 / p) - 1) * (8 * (eLpNorm (fun y => α + β * y) (ENNReal.ofReal p)
      (volume.restrict (Icc a (a + ℓ)))).toReal) := by
    rw [← hrp] at key
    have hℓ' : 0 < ℓ := hℓ
    nlinarith [mul_pos hpos hℓ']
  linarith

end FormalizacaoEmb
