import Mathlib

/-!
# Núcleo da projeção em afins (Lema 5.1): identidade com `kL` e `kR`

Sobre um intervalo `[a, a+ℓ]`, o núcleo `K(x,y) = ℓ^{-1}(1 + 3(2u_x-1)(2u_y-1))`, com
`u_x = (x-a)/ℓ`, define o operador `T h(x) = ∫ K(x,y) h(y) dy`. Provam-se:

* `K` é simétrico;
* `T h` é afim em `x`, para toda `h` integrável (imagem = afins);
* `T g = g` para toda `g` afim (reprodução de afins).

Logo `T` é a projeção ortogonal em `L²([a,a+ℓ])` sobre as funções afins (idempotente,
auto-adjunto, com imagem igual às afins). Os núcleos de `QuasiLocal` são os valores nos extremos:
`kL a ℓ y = K(a,y)` e `kR a ℓ y = K(a+ℓ,y)`.
-/

open MeasureTheory Set intervalIntegral

namespace FormalizacaoKer

/-- núcleo `K(x,y)` da projeção em afins sobre `[a, a+ℓ]`. -/
noncomputable def Kf (a ℓ x y : ℝ) : ℝ :=
  (1 + 3 * (2 * ((x - a) / ℓ) - 1) * (2 * ((y - a) / ℓ) - 1)) / ℓ

/-- `kL` de `QuasiLocal` é `K` no extremo esquerdo. -/
theorem kL_eq_Kf (a ℓ y : ℝ) : (4 - 6 * ((y - a) / ℓ)) / ℓ = Kf a ℓ a y := by
  unfold Kf
  simp only [sub_self, zero_div, mul_zero]
  ring

/-- `kR` de `QuasiLocal` é `K` no extremo direito. -/
theorem kR_eq_Kf (a ℓ y : ℝ) (hℓ : ℓ ≠ 0) :
    (6 * ((y - a) / ℓ) - 2) / ℓ = Kf a ℓ (a + ℓ) y := by
  unfold Kf
  have h1 : (a + ℓ - a) / ℓ = 1 := by field_simp; ring
  rw [h1]
  ring

/-- simetria do núcleo. -/
theorem Kf_symm (a ℓ x y : ℝ) : Kf a ℓ x y = Kf a ℓ y x := by
  unfold Kf; ring

/-- integral sobre `Icc` como integral de intervalo. -/
lemma integral_Icc_eq (a b : ℝ) (hab : a ≤ b) (φ : ℝ → ℝ) :
    ∫ y in Icc a b, φ y = ∫ y in a..b, φ y := by
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

/-- **Reprodução de afins:** `∫_{[a,a+ℓ]} K(x,y)(α+βy) dy = α + βx`. -/
theorem reproduce_affine {a ℓ : ℝ} (hℓ : 0 < ℓ) (x α β : ℝ) :
    ∫ y in Icc a (a + ℓ), Kf a ℓ x y * (α + β * y) = α + β * x := by
  rw [integral_Icc_eq a (a + ℓ) (by linarith)]
  -- `K(x,y) = k0 + k1 y`, com `k0, k1` independentes de `y`
  obtain ⟨k0, k1, hk0, hk1, hK⟩ : ∃ k0 k1 : ℝ,
      k0 = (1 - 3 * (2 * ((x - a) / ℓ) - 1)) / ℓ - 6 * (2 * ((x - a) / ℓ) - 1) * a / ℓ ^ 2 ∧
      k1 = 6 * (2 * ((x - a) / ℓ) - 1) / ℓ ^ 2 ∧
      ∀ y, Kf a ℓ x y = k0 + k1 * y :=
    ⟨_, _, rfl, rfl, fun y => by unfold Kf; field_simp; ring⟩
  simp_rw [hK]
  have hF : ∀ y : ℝ, HasDerivAt
      (fun y => k0 * α * y + (k0 * β + k1 * α) * y ^ 2 / 2 + k1 * β * y ^ 3 / 3)
      ((k0 + k1 * y) * (α + β * y)) y := by
    intro y
    have h1 : HasDerivAt (fun y => k0 * α * y) (k0 * α) y := by
      simpa using (hasDerivAt_id y).const_mul (k0 * α)
    have h2 : HasDerivAt (fun y => (k0 * β + k1 * α) * y ^ 2 / 2) ((k0 * β + k1 * α) * y) y := by
      have := ((hasDerivAt_pow 2 y).const_mul (k0 * β + k1 * α)).div_const 2
      convert this using 1; simp; ring
    have h3 : HasDerivAt (fun y => k1 * β * y ^ 3 / 3) (k1 * β * y ^ 2) y := by
      have := ((hasDerivAt_pow 3 y).const_mul (k1 * β)).div_const 3
      convert this using 1; simp; ring
    have := (h1.add h2).add h3
    convert this using 1; ring
  have hint : IntervalIntegrable (fun y => (k0 + k1 * y) * (α + β * y)) volume a (a + ℓ) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hF y) hint]
  subst hk0 hk1
  field_simp
  ring

/-- **Imagem em afins:** `x ↦ ∫ K(x,y) h(y) dy` é afim, para `h` integrável. -/
theorem range_affine {a ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ → ℝ}
    (hi : IntegrableOn h (Icc a (a + ℓ))) :
    ∃ α β : ℝ, ∀ x : ℝ, ∫ y in Icc a (a + ℓ), Kf a ℓ x y * h y = α + β * x := by
  set P : ℝ → ℝ := fun y => (1 - 3 * (2 * ((y - a) / ℓ) - 1)) / ℓ with hP
  set Q : ℝ → ℝ := fun y => 6 * (2 * ((y - a) / ℓ) - 1) / ℓ with hQ
  have hPc : Continuous P := by rw [hP]; fun_prop
  have hQc : Continuous Q := by rw [hQ]; fun_prop
  have hPi : IntegrableOn (fun y => P y * h y) (Icc a (a + ℓ)) :=
    (hi.mul_continuousOn hPc.continuousOn isCompact_Icc).congr_fun
      (fun y _ => mul_comm _ _) measurableSet_Icc
  have hQi : IntegrableOn (fun y => Q y * h y) (Icc a (a + ℓ)) :=
    (hi.mul_continuousOn hQc.continuousOn isCompact_Icc).congr_fun
      (fun y _ => mul_comm _ _) measurableSet_Icc
  have hkey (x : ℝ) : ∫ y in Icc a (a + ℓ), Kf a ℓ x y * h y =
      (∫ y in Icc a (a + ℓ), P y * h y) + ((x - a) / ℓ) * ∫ y in Icc a (a + ℓ), Q y * h y := by
    rw [← MeasureTheory.integral_const_mul, ← integral_add hPi (hQi.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Icc (fun y _ => ?_)
    simp only [Kf, hP, hQ]
    field_simp
    ring
  refine ⟨(∫ y in Icc a (a + ℓ), P y * h y) - a * (∫ y in Icc a (a + ℓ), Q y * h y) / ℓ,
    (∫ y in Icc a (a + ℓ), Q y * h y) / ℓ, ?_⟩
  intro x
  rw [hkey x]
  field_simp
  ring

/-- **Núcleo da projeção em afins.** `K` é simétrico, reproduz afins e tem imagem afim; logo o
operador `h ↦ ∫ K(·,y) h(y) dy` é a projeção ortogonal de `L²([a,a+ℓ])` sobre as funções afins. -/
theorem kernel_is_affine_projection {a ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∀ x y : ℝ, Kf a ℓ x y = Kf a ℓ y x) ∧
    (∀ x α β : ℝ, ∫ y in Icc a (a + ℓ), Kf a ℓ x y * (α + β * y) = α + β * x) ∧
    (∀ h : ℝ → ℝ, IntegrableOn h (Icc a (a + ℓ)) →
      ∃ α β : ℝ, ∀ x : ℝ, ∫ y in Icc a (a + ℓ), Kf a ℓ x y * h y = α + β * x) :=
  ⟨Kf_symm a ℓ, fun x α β => reproduce_affine hℓ x α β,
    fun _ hi ↦ range_affine hℓ hi⟩

end FormalizacaoKer
