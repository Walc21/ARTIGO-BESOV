import Formalizacao.Whitney11

/-!
# Lema 5.3 (Whitney em partições de `L^p`) — M5 concluído

`whitney_lp : 1 ≤ p → ∃ C_W ≥ 0, WhitneyLp p C_W`. A hipótese `WhitneyLp` do
Corolário 5.4 deixa de ser hipótese: ela é um teorema.
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoGrid

namespace FormalizacaoW

open FormalizacaoCor FormalizacaoLp

/-- `Σ_k ∫_{I_k} |W(·; δ)|^p ≤ 4 ω^p` -/
lemma sum_T_le {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ} (hfm : Measurable f) :
    ∑ k ∈ Finset.range n, ∫⁻ x in Iset n k, ‖Wt f x (dl n)‖ₑ ^ p ≤
      4 * (wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f) ^ p := by
  have hd := dl_pos (n := n) (by omega)
  have hw : |dl n| ≤ 1 / (4 * (n : ℝ)) := by
    rw [abs_of_pos hd]; rfl
  have h1 := sum_lintegral_le hn (F := fun x => ‖Wt f x (dl n)‖ₑ ^ p)
    (Wt_measurable hfm _ p) (S := Iset n) (fun k => measurableSet_Icc)
    (fun k _ => Iset_sub_J hn k) (U := Icc |dl n| (1 - |dl n|)) measurableSet_Icc
    (fun k _ => Iset_sub_rho hn k (by rw [abs_of_pos hd]))
  exact h1.trans (mul_le_mul_left' (Wt_global hn hp (f := f) hw) _)

/-- **Lema 5.3 (Whitney em partições de `L^p`).** -/
theorem whitney_lp {p : ℝ} (hp : 1 ≤ p) : ∃ CW : ℝ, 0 ≤ CW ∧ WhitneyLp p CW := by
  have hp0 : 0 < p := by linarith
  set Kt : ℝ≥0∞ := 4 * K1 p + 4 * K2 p with hKt
  have hKtfin : Kt ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) (K1_ne_top hp),
      ENNReal.mul_ne_top (by norm_num) (K2_ne_top hp)⟩
  refine ⟨Kt.toReal ^ (1 / p), by positivity, ?_⟩
  intro n hn f hfm hfi _
  have hd := dl_pos (n := n) (by omega)
  set B := (wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f) ^ p with hB
  set c0 : ℝ≥0∞ := ENNReal.ofReal ((1 / (2 * (dl n) ^ 2)) ^ p * (dl n) ^ (2 * (p - 1))) with hc0
  -- `c₀ · δ · δ ≤ 1`
  have hc0le : c0 * (ENNReal.ofReal (dl n) * ENNReal.ofReal (dl n)) ≤ 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), hc0, ← ENNReal.ofReal_mul (by positivity)]
    rw [c0_delta hd]
    calc ENNReal.ofReal ((1 / 2 : ℝ) ^ p) ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal (Real.rpow_le_one (by norm_num) (by norm_num) hp0.le)
      _ = 1 := ENNReal.ofReal_one
  have hsum : ∑ k ∈ Finset.range n, Ek p f n k ^ p ≤ Kt * B := by
    calc ∑ k ∈ Finset.range n, Ek p f n k ^ p
        ≤ ∑ k ∈ Finset.range n, (K1 p * (∫⁻ x in Iset n k, ‖Wt f x (dl n)‖ₑ ^ p) +
            K2 p * (c0 * ∫⁻ s in Ioc 0 (dl n), ∫⁻ r in Ioc 0 (dl n), ∫⁻ x in Iset n k,
              Fw f (dl n) p x s r)) :=
          Finset.sum_le_sum (fun k _ => Ek_bound hn hp hfm hfi k)
      _ = K1 p * (∑ k ∈ Finset.range n, ∫⁻ x in Iset n k, ‖Wt f x (dl n)‖ₑ ^ p) +
            K2 p * (c0 * ∑ k ∈ Finset.range n, ∫⁻ s in Ioc 0 (dl n), ∫⁻ r in Ioc 0 (dl n),
              ∫⁻ x in Iset n k, Fw f (dl n) p x s r) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ K1 p * (4 * B) + K2 p * (c0 * (4 * B * ENNReal.ofReal (dl n) * ENNReal.ofReal (dl n))) := by
          gcongr
          · exact sum_T_le hn hp hfm
          · exact sum_Fint_le hn hp hfm
      _ ≤ K1 p * (4 * B) + K2 p * (4 * B) := by
          have hmul : c0 * (4 * B * ENNReal.ofReal (dl n) * ENNReal.ofReal (dl n)) ≤ 4 * B := by
            calc c0 * (4 * B * ENNReal.ofReal (dl n) * ENNReal.ofReal (dl n))
                = 4 * B * (c0 * (ENNReal.ofReal (dl n) * ENNReal.ofReal (dl n))) := by ring
              _ ≤ 4 * B * 1 := mul_le_mul_left' hc0le _
              _ = 4 * B := mul_one _
          exact add_le_add le_rfl (mul_le_mul_left' hmul _)
      _ = Kt * B := by rw [hKt]; ring
  calc (∑ k ∈ Finset.range n, Ek p f n k ^ p) ^ (1 / p) ≤ (Kt * B) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hsum (by positivity)
    _ = Kt ^ (1 / p) * B ^ (1 / p) := ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal (Kt.toReal ^ (1 / p)) *
          wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f := by
        congr 1
        · rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
            ENNReal.ofReal_toReal hKtfin]
        · rw [hB, ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

end FormalizacaoW
