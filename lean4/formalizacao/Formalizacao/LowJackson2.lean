import Formalizacao.LowJackson
import Formalizacao.LowSup

/-!
# Regimes `s ≤ 1/p`, parte 5: Jackson racional sem continuidade

`jackson_low` é o `Teorema lp:thm:jackson-low` do artigo: para `f ∈ B^s_{p,q}` mensurável,
`s ≤ 1/p`, existem `C_W, K` (dependendo de `f`) tais que, para `r ≥ 1`, `r ≤ e` e todo inteiro
`H ≥ 8 (K Λ_r + 1) 2^e`, há `g ∈ A_{2^r,H}` com
`‖f - g‖_p ≤ 9 C_W ω_p(f, 2^{-r}) + 1/(2·2^e)`.
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoGrid FormalizacaoLp

namespace FormalizacaoLow

/-- `A_{n,H(N)} ⊆ Σ_N^H` quando `n ≤ N`. -/
theorem classNH_le_sigma (H : ℕ → ℕ) {n N : ℕ} (hn : n ≤ N) :
    classNH n (H N) ⊆ Pendencias.Agenda.Sigma H N := by
  rintro g ⟨T, hT, rfl⟩
  exact Or.inr ⟨T, ⟨hT.1, hT.2.1.trans hn, hT.2.2⟩, rfl⟩

theorem jackson_low {p s : ℝ} (hp : 1 ≤ p) (hs : s ≤ 1 / p) {q : ℝ≥0∞} (hq : 0 < q)
    {f : ℝ → ℝ} (hf : Measurable f) (hbes : f ∈ besovP (ENNReal.ofReal p) s q) :
    ∃ CW K : ℝ, 0 ≤ CW ∧ 1 ≤ K ∧ ∀ r e : ℕ, 1 ≤ r → r ≤ e → ∀ H : ℕ,
      8 * (K * Lam p s q r + 1) * 2 ^ e ≤ (H : ℝ) →
      ∃ g ∈ classNH (2 ^ r) H, eLpNorm (f - g) (ENNReal.ofReal p) vol01 ≤
        9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f +
          ENNReal.ofReal (1 / (2 * 2 ^ e)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨hfin', _⟩ := (FormalizacaoRed.mem_besovP_iff _ _ _ _).1 hbes
  have hfin : Np p f (Icc 0 1) < ⊤ := hfin'
  have hfi : IntegrableOn f (Icc 0 1) := by
    have hmem : MemLp f (ENNReal.ofReal p) (volume.restrict (Icc (0 : ℝ) 1)) :=
      ⟨hf.aestronglyMeasurable, hfin'⟩
    exact hmem.integrable hp1
  obtain ⟨CW, hCW, hq'⟩ := FormalizacaoW.quasi_error_unc hp
  obtain ⟨K, hK1, hKb⟩ := lam_bound hp hs hq hf hbes
  refine ⟨CW, K, hCW, hK1, fun r e hr hre H hH => ?_⟩
  have hL : 1 ≤ Lam p s q r := one_le_Lam p s q hr hs
  have hM : 0 ≤ K * Lam p s q r := mul_nonneg (by linarith) (by linarith)
  have hr2 : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  exact FormalizacaoJ.lp_jackson_low_core hp hq' hf hfi hfin hM hr2 hre
    (fun j hj => hKb r hr j hj) hH

end FormalizacaoLow
