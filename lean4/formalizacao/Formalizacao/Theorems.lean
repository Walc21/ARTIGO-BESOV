import Formalizacao.Reductions
import Formalizacao.Schedules

/-!
# Reduções condicionais: Conjectura 1 a partir de `J_p`

Para cada caso da Conjectura 1 (`Conj1Endpoint`, `Conj1Subcritical`, `Conj1Critical`),
prova-se que a hipótese `J_p` implica a igualdade, para funções mensuráveis. A inclusão
`R ⊆ B` é `stratum_subset_besov_conn` (sem hipótese); a inclusão `B ⊆ R` é
`besov_subset_stratum`, com a agenda correspondente. Também se prova o caso com a
agenda alternativa `H̃_{s,η}` (observação do rascunho sobre `lp:eq:conj-critical`).
-/

open scoped ENNReal
open MeasureTheory Set

namespace FormalizacaoThm

open FormalizacaoLp FormalizacaoLq FormalizacaoRed FormalizacaoSched

/-- Os elementos de qualquer `Σ_N^H` são mensuráveis. -/
theorem sigma_meas_all (H : ℕ → ℕ) : ∀ N : ℕ, ∀ g ∈ Pendencias.Agenda.Sigma H N,
    Measurable g :=
  fun _ _ hg => measurable_sigma hg

/-- **Conjectura 1, caso `q = ∞`**, a partir de `J_p`. -/
theorem conj1_endpoint_of_J {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s) :
    Conj1Endpoint p s := by
  intro f hf
  have hq : (0 : ℝ≥0∞) < ⊤ := ENNReal.zero_lt_top
  have hH : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (max 1 s) ≤
      (Pendencias.Agenda.Hsk s 0 N : ℝ) := fun N hN => Hsk_low (le_refl 0) N hN
  constructor
  · intro hbes
    have hW : lqNorm ⊤ (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) /
        (Pendencias.Agenda.Hsk s 0 (2 ^ (k + 1)) : ℝ≥0∞)) < ⊤ := by
      rw [lqNorm, if_pos rfl]
      exact lt_of_le_of_lt (iSup_le fun k => weight_bdd _ hH k) ENNReal.ofReal_lt_top
    exact besov_subset_stratum hp hJ hq (Pendencias.Agenda.Hsk s 0) hH hW hf hbes
  · intro hstr
    exact stratum_subset_besov_conn hp _ (sigma_meas_all _) s ⊤ hq hf hstr

/-- **Conjectura 1, caso `0 < q < ∞`, `s < 1`** (subcrítico), a partir de `J_p`. -/
theorem conj1_subcritical_of_J {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s)
    (hs : s < 1) {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) :
    Conj1Subcritical p s q := by
  intro f hf
  have hH : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (max 1 s) ≤
      (Pendencias.Agenda.Hsk s 0 N : ℝ) := fun N hN => Hsk_low (le_refl 0) N hN
  have hmax : max 1 s = 1 := max_eq_left hs.le
  have hH1 : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (1 : ℝ) ≤
      (Pendencias.Agenda.Hsk s 0 N : ℝ) := by
    intro N hN
    have := hH N hN
    rwa [hmax] at this
  have hsa : s < 1 := hs
  have hneg : s - 1 < 0 := by linarith
  have hρ1 : (2 : ℝ) ^ (s - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
  have hρ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (s - 1) := by positivity
  have hW : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) /
      (Pendencias.Agenda.Hsk s 0 (2 ^ (k + 1)) : ℝ≥0∞)) < ⊤ :=
    lq_of_geom_le hq0 hqt (C := (2 : ℝ) ^ (s - 1) / 8) (ρ := (2 : ℝ) ^ (s - 1))
      (by positivity) hρ0 hρ1 (fun k => weight_geom _ hsa hH1 k)
  constructor
  · intro hbes
    exact besov_subset_stratum hp hJ hq0 (Pendencias.Agenda.Hsk s 0) hH hW hf hbes
  · intro hstr
    exact stratum_subset_besov_conn hp _ (sigma_meas_all _) s q hq0 hf hstr

/-- **Conjectura 1, caso `0 < q < ∞`, `1 ≤ s`, `κ q > 1`** (crítico), a partir de `J_p`. -/
theorem conj1_critical_of_J {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s)
    (hs : 1 ≤ s) {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) {κ : ℝ} (hκ : 0 ≤ κ)
    (hκq : 1 < κ * q.toReal) :
    Conj1Critical p s q κ := by
  intro f hf
  have hH : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (max 1 s) ≤
      (Pendencias.Agenda.Hsk s κ N : ℝ) := fun N hN => Hsk_low hκ N hN
  have hD : 0 ≤ 1 / 8 * (Real.log 2) ^ (-κ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _)
  have hW : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) /
      (Pendencias.Agenda.Hsk s κ (2 ^ (k + 1)) : ℝ≥0∞)) < ⊤ :=
    lq_of_poly_le hq0 hqt hD hκq (fun k => weight_poly hs hκ k)
  constructor
  · intro hbes
    exact besov_subset_stratum hp hJ hq0 (Pendencias.Agenda.Hsk s κ) hH hW hf hbes
  · intro hstr
    exact stratum_subset_besov_conn hp _ (sigma_meas_all _) s q hq0 hf hstr

/-- **Conjectura 1 com a agenda `H̃_{s,η}`**, `0 < q < ∞`, `η > 0`, a partir de `J_p`. -/
theorem conj1_tilde_of_J {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s)
    {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) {η : ℝ} (hη : 0 < η) (f : ℝ → ℝ)
    (hf : Measurable f) :
    f ∈ besovP p s q ↔ f ∈ stratumP p s q (Pendencias.Agenda.Sigma
      (fun N => Pendencias.Jackson.HtilK 0 0 s η N)) := by
  have hH : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (max 1 s) ≤
      (Pendencias.Jackson.HtilK 0 0 s η N : ℝ) := fun N hN => Htil_low hη.le N hN
  have ha : s < max 1 (s + η) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hH' : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (max 1 (s + η)) ≤
      (Pendencias.Jackson.HtilK 0 0 s η N : ℝ) := by
    intro N hN
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h1 : (N : ℝ) ^ (max 1 (s + η)) ≤ ((N : ℝ) + 1) ^ (max 1 (s + η)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith)
        (le_trans zero_le_one (le_max_left _ _))
    have h2 := Htil_real_ge s η N
    linarith
  have hneg : s - max 1 (s + η) < 0 := by linarith
  have hρ1 : (2 : ℝ) ^ (s - max 1 (s + η)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
  have hρ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (s - max 1 (s + η)) := by positivity
  have hW : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) /
      (Pendencias.Jackson.HtilK 0 0 s η (2 ^ (k + 1)) : ℝ≥0∞)) < ⊤ :=
    lq_of_geom_le hq0 hqt (C := (2 : ℝ) ^ (s - max 1 (s + η)) / 8)
      (ρ := (2 : ℝ) ^ (s - max 1 (s + η))) (by positivity) hρ0 hρ1
      (fun k => weight_geom _ ha hH' k)
  constructor
  · intro hbes
    exact besov_subset_stratum hp hJ hq0 (fun N => Pendencias.Jackson.HtilK 0 0 s η N) hH hW
      hf hbes
  · intro hstr
    exact stratum_subset_besov_conn hp _ (sigma_meas_all _) s q hq0 hf hstr

end FormalizacaoThm
