import Formalizacao.Whitney8

/-!
# Whitney em `L^p` (M5), parte 9: cota global pelo módulo `ω_p`
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoGrid

namespace FormalizacaoW

open FormalizacaoCor FormalizacaoLp

/-- **`∫ |W(·; w)|^p ≤ ω_p^p`.** Para `|w| ≤ 1/(4n)`, `n ≥ 2`. -/
lemma Wt_global {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ} {w : ℝ}
    (hw : |w| ≤ 1 / (4 * (n : ℝ))) :
    ∫⁻ x in Icc |w| (1 - |w|), ‖Wt f x w‖ₑ ^ p ≤
      (wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f) ^ p := by
  have hp0 : 0 < p := by linarith
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set ρ : ℝ := |w| with hρ
  have hWt : ∀ x, Wt f x w = Wt f x ρ := by
    intro x
    rcases abs_cases w with ⟨h, _⟩ | ⟨h, _⟩
    · rw [hρ, h]
    · rw [hρ, h]; unfold Wt; ring_nf
  simp_rw [hWt]
  by_cases h0 : ρ = 0
  · have : ∀ x, Wt f x ρ = 0 := by intro x; rw [h0]; unfold Wt; simp; ring
    simp [this, ENNReal.zero_rpow_of_pos hp0]
  · have hρpos : 0 < ρ := lt_of_le_of_ne (abs_nonneg w) (Ne.symm h0)
    have hρle : ρ ≤ min (1 / (n : ℝ)) (1 / 2) := by
      refine le_min ?_ ?_
      · calc ρ ≤ 1 / (4 * (n : ℝ)) := hw
          _ ≤ 1 / (n : ℝ) := by
            apply one_div_le_one_div_of_le (by linarith); linarith
      · calc ρ ≤ 1 / (4 * (n : ℝ)) := hw
          _ ≤ 1 / 2 := by
            apply one_div_le_one_div_of_le (by norm_num); linarith
    have hshift := lintegral_Icc_shift (fun x => ‖Wt f x ρ‖ₑ ^ p) 0 (1 - 2 * ρ) ρ
    have e0 : (0 : ℝ) + ρ = ρ := by ring
    have e1 : 1 - 2 * ρ + ρ = 1 - ρ := by ring
    rw [e0, e1] at hshift
    rw [← hshift]
    have hd : ∀ y, Wt f (y + ρ) ρ = diff2 ρ f y := by
      intro y
      have e2 : y + ρ + ρ = y + 2 * ρ := by ring
      have e3 : y + ρ - ρ = y := by ring
      unfold Wt diff2
      rw [e2, e3]; ring
    simp_rw [hd]
    have hN := FormalizacaoCor.Np_rpow_eq hp (diff2 ρ f) (Icc 0 (1 - 2 * ρ))
    rw [← hN]
    refine ENNReal.rpow_le_rpow ?_ hp0.le
    unfold Np wtP
    exact le_iSup₂ (f := fun (h : ℝ) (_ : h ∈ Ioc 0 (min (1 / (n : ℝ)) (1 / 2))) =>
      eLpNorm (diff2 h f) (ENNReal.ofReal p) (volume.restrict (Icc 0 (1 - 2 * h)))) ρ
      ⟨hρpos, hρle⟩

end FormalizacaoW
