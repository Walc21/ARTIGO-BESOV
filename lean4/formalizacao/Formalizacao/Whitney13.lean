import Formalizacao.Whitney12
import Formalizacao.Lemma55e

/-!
# Consequências incondicionais do Lema 5.3 (M5)

Com `whitney_lp`, o Corolário 5.4 e o Lema 5.5 deixam de depender da hipótese `WhitneyLp`.
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoGrid

namespace FormalizacaoW

open FormalizacaoCor FormalizacaoLp

/-- **Corolário 5.4, incondicional.** -/
theorem quasi_error_unc {p : ℝ} (hp : 1 ≤ p) :
    ∃ CW : ℝ, 0 ≤ CW ∧ ∀ n : ℕ, 2 ≤ n → ∀ f : ℝ → ℝ, Measurable f →
      IntegrableOn f (Icc 0 1) → Np p f (Icc 0 1) < ⊤ →
      Np p (fun x => f x - Q n f x) (Icc 0 1) ≤
        9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f := by
  obtain ⟨CW, hCW, hW⟩ := whitney_lp hp
  exact ⟨CW, hCW, fun n hn f hf hfi hfin => FormalizacaoCor.quasi_error hp hW hn hf hfi hfin⟩

/-- **Lema 5.5(a), incondicional:** `G` é contínua em `[0,1]`. -/
theorem Glim_continuousOn_unc {p s : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ} (hf : Measurable f)
    (hfi : IntegrableOn f (Icc 0 1)) (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) :
    ContinuousOn (FormalizacaoL55c.Glim f) (Icc 0 1) := by
  obtain ⟨CW, hCW, hW⟩ := whitney_lp hp
  exact FormalizacaoL55c.Glim_continuousOn hp hW hCW hf hfi hfin hS hbS hs

/-- **Lema 5.5(a), incondicional:** `f = G` quase sempre em `[0,1]`. -/
theorem ae_eq_Glim_unc {p s : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ} (hf : Measurable f)
    (hfi : IntegrableOn f (Icc 0 1)) (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), f x = FormalizacaoL55c.Glim f x := by
  obtain ⟨CW, hCW, hW⟩ := whitney_lp hp
  exact FormalizacaoL55c.ae_eq_Glim hp hW hCW hf hfi hfin hS hbS hs

/-- **Lema 5.5(b), incondicional, regime `s - 1/p < 1`.** -/
theorem modulus_lt1_unc {p s : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ} (hf : Measurable f)
    (hfi : IntegrableOn f (Icc 0 1)) (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) (ha : s - 1 / p < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ x y : ℝ, x ∈ Icc (0 : ℝ) 1 →
      y ∈ Icc (0 : ℝ) 1 → |x - y| ≤ t →
      |FormalizacaoL55c.Glim f x - FormalizacaoL55c.Glim f y| ≤ C * t ^ (s - 1 / p) := by
  obtain ⟨CW, hCW, hW⟩ := whitney_lp hp
  exact FormalizacaoL55e.modulus_lt1 hp hW hCW hf hfi hfin hS hbS hs ha

/-- **Lema 5.5(b), incondicional, regime `s - 1/p = 1`.** -/
theorem modulus_eq1_unc {p s : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ} (hf : Measurable f)
    (hfi : IntegrableOn f (Icc 0 1)) (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) (ha : s - 1 / p = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ x y : ℝ, x ∈ Icc (0 : ℝ) 1 →
      y ∈ Icc (0 : ℝ) 1 → |x - y| ≤ t →
      |FormalizacaoL55c.Glim f x - FormalizacaoL55c.Glim f y| ≤
        C * (t * (1 + Real.log (1 / t))) := by
  obtain ⟨CW, hCW, hW⟩ := whitney_lp hp
  exact FormalizacaoL55e.modulus_eq1 hp hW hCW hf hfi hfin hS hbS hs ha

/-- **Lema 5.5(b), incondicional, regime `s - 1/p > 1`.** -/
theorem modulus_gt1_unc {p s : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ} (hf : Measurable f)
    (hfi : IntegrableOn f (Icc 0 1)) (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) (ha : 1 < s - 1 / p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ x y : ℝ, x ∈ Icc (0 : ℝ) 1 →
      y ∈ Icc (0 : ℝ) 1 → |x - y| ≤ t →
      |FormalizacaoL55c.Glim f x - FormalizacaoL55c.Glim f y| ≤ C * t := by
  obtain ⟨CW, hCW, hW⟩ := whitney_lp hp
  exact FormalizacaoL55e.modulus_gt1 hp hW hCW hf hfi hfin hS hbS hs ha

end FormalizacaoW
