import Formalizacao.Whitney10

/-!
# Whitney em `L^p` (M5), parte 11: a soma e a hipótese `WhitneyLp`

`(Σ_k E(f,J_k)_p^p)^{1/p} ≤ C_W ω_p(f, 1/n)`.
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoGrid

namespace FormalizacaoW

open FormalizacaoCor FormalizacaoLp

lemma meas_inner {h : ℝ → ℝ} (hh : Measurable h) (δ p : ℝ) (S : Set ℝ) :
    Measurable (fun s : ℝ => ∫⁻ r in Ioc 0 δ, ∫⁻ x in S, Fw h δ p x s r) := by
  have hF := Fw_measurable hh δ p
  have h3 : Measurable (fun q : (ℝ × ℝ) × ℝ => Fw h δ p q.2 q.1.1 q.1.2) :=
    hF.comp (by fun_prop : Measurable (fun q : (ℝ × ℝ) × ℝ => (q.2, q.1.1, q.1.2)))
  have h4 : Measurable (fun q : ℝ × ℝ => ∫⁻ x in S, Fw h δ p x q.1 q.2) :=
    h3.lintegral_prod_right' (ν := volume.restrict S)
  exact h4.lintegral_prod_right' (ν := volume.restrict (Ioc 0 δ))

lemma meas_inner2 {h : ℝ → ℝ} (hh : Measurable h) (δ p s : ℝ) (S : Set ℝ) :
    Measurable (fun r : ℝ => ∫⁻ x in S, Fw h δ p x s r) := by
  have hF := Fw_measurable hh δ p
  have h3 : Measurable (fun q : ℝ × ℝ => Fw h δ p q.2 s q.1) :=
    hF.comp (by fun_prop : Measurable (fun q : ℝ × ℝ => (q.2, s, q.1)))
  exact h3.lintegral_prod_right' (ν := volume.restrict S)

/-- troca da soma finita com as integrais em `s` e `r` -/
lemma sum_Fint {h : ℝ → ℝ} (hh : Measurable h) (δ p : ℝ) (n : ℕ) (S : ℕ → Set ℝ) :
    ∑ k ∈ Finset.range n, ∫⁻ s in Ioc 0 δ, ∫⁻ r in Ioc 0 δ, ∫⁻ x in S k, Fw h δ p x s r =
      ∫⁻ s in Ioc 0 δ, ∫⁻ r in Ioc 0 δ, ∑ k ∈ Finset.range n, ∫⁻ x in S k, Fw h δ p x s r := by
  rw [← lintegral_finset_sum _ (fun k _ => meas_inner hh δ p (S k))]
  refine lintegral_congr (fun s => ?_)
  rw [← lintegral_finset_sum _ (fun k _ => meas_inner2 hh δ p s (S k))]

/-- `(1/(2δ²))^p · δ^{2(p-1)} · (δ·δ) = (1/2)^p` -/
lemma c0_delta {δ p : ℝ} (hδ : 0 < δ) :
    (1 / (2 * δ ^ 2)) ^ p * δ ^ (2 * (p - 1)) * (δ * δ) = (1 / 2) ^ p := by
  have h2 : (δ ^ 2) ^ p = δ ^ (2 * p) := by
    rw [← Real.rpow_natCast δ 2, ← Real.rpow_mul hδ.le]; norm_num
  have h3 : (1 / δ ^ 2) ^ p = 1 / δ ^ (2 * p) := by
    rw [Real.div_rpow zero_le_one (by positivity), Real.one_rpow, h2]
  have h5 : δ ^ (2 * (p - 1)) * (δ * δ) = δ ^ (2 * p) := by
    have : δ * δ = δ ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
    rw [this, ← Real.rpow_add hδ]; congr 1; ring
  have h6 : (1 / (2 * δ ^ 2)) ^ p = (1 / 2) ^ p * (1 / δ ^ 2) ^ p := by
    rw [show 1 / (2 * δ ^ 2) = (1 / 2) * (1 / δ ^ 2) by field_simp]
    exact Real.mul_rpow (by norm_num) (by positivity)
  have h4 : δ ^ (2 * p) ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
  rw [h6, h3, mul_assoc, mul_assoc, h5]
  field_simp

lemma Wt_measurable {f : ℝ → ℝ} (hfm : Measurable f) (w p : ℝ) :
    Measurable (fun x : ℝ => ‖Wt f x w‖ₑ ^ p) := by
  unfold Wt
  exact (((hfm.comp (by fun_prop)).add (hfm.comp (by fun_prop))).sub
    (hfm.const_mul 2)).enorm.pow_const p

/-- `Σ_k ∫_s ∫_r ∫_{I_k} |W|^p ≤ 4 ω^p δ²` -/
lemma sum_Fint_le {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ} (hfm : Measurable f) :
    ∑ k ∈ Finset.range n, ∫⁻ s in Ioc 0 (dl n), ∫⁻ r in Ioc 0 (dl n), ∫⁻ x in Iset n k,
        Fw f (dl n) p x s r ≤
      4 * (wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f) ^ p *
        ENNReal.ofReal (dl n) * ENNReal.ofReal (dl n) := by
  rw [sum_Fint hfm (dl n) p n (Iset n)]
  have hd := dl_pos (n := n) (by omega)
  set B := (wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f) ^ p with hB
  have bound : ∀ s ∈ Ioc 0 (dl n), ∀ r ∈ Ioc 0 (dl n),
      ∑ k ∈ Finset.range n, ∫⁻ x in Iset n k, Fw f (dl n) p x s r ≤ 4 * B := by
    intro s hs r hr
    have hw : |s + r - dl n| ≤ 1 / (4 * (n : ℝ)) := by
      have : dl n = 1 / (4 * (n : ℝ)) := rfl
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2, hr.1, hr.2]
    have hrho : |s + r - dl n| ≤ dl n := hw
    have h1 := sum_lintegral_le hn (F := fun x => ‖Wt f x (s + r - dl n)‖ₑ ^ p)
      (Wt_measurable hfm _ p) (S := Iset n) (fun k => measurableSet_Icc)
      (fun k _ => Iset_sub_J hn k) (U := Icc |s + r - dl n| (1 - |s + r - dl n|))
      measurableSet_Icc (fun k _ => Iset_sub_rho hn k hrho)
    have h2 := Wt_global hn hp (f := f) hw
    unfold Fw
    exact h1.trans (mul_le_mul_left' h2 _)
  calc ∫⁻ s in Ioc 0 (dl n), ∫⁻ r in Ioc 0 (dl n), ∑ k ∈ Finset.range n,
        ∫⁻ x in Iset n k, Fw f (dl n) p x s r
      ≤ ∫⁻ s in Ioc 0 (dl n), ∫⁻ r in Ioc 0 (dl n), 4 * B :=
        setLIntegral_mono' measurableSet_Ioc (fun s hs =>
          setLIntegral_mono' measurableSet_Ioc (fun r hr => bound s hs r hr))
    _ = 4 * B * ENNReal.ofReal (dl n) * ENNReal.ofReal (dl n) := by
        simp only [setLIntegral_const, Real.volume_Ioc, sub_zero]

end FormalizacaoW
