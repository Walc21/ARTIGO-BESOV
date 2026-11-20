import Formalizacao.LowTransfer
import Formalizacao.LowShift

/-!
# Regimes `s ≤ 1/p`, parte 9: Teoremas 3.1 (ii), (iii) e 3.2 nesses regimes

Para `1 ≤ p < ∞` (escrito `p : ℝ`, com `ENNReal.ofReal p`), valem:

* **`s < 1/p`**, agenda `Hsk (1 + 1/p - s) 0 N = ⌈8 (N+1)^{1+1/p-s}⌉`, todo `0 < q ≤ ∞`:
  `conj1_low` (igualdade `B = R(Σ^H)`) e `conj2_low` (estabilidade por inclusão de redes).
* **`s = 1/p`**, agenda `Hsk 1 (θ_q + κ) N = ⌈8 (N+1) [log(eN)]^{θ_q+κ}⌉`, `κ ≥ 0`, com `κ q > 1`
  quando `p = 1` e `q < ∞`: `conj1_diag` e `conj2_diag`.

Em ambos os casos a inclusão `B ⊆ R` é `besov_subset_stratum_low` e a inclusão reversa é
`stratum_subset_besov_conn`.
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoLp FormalizacaoLq FormalizacaoRed FormalizacaoStab

namespace FormalizacaoLow

lemma hW_geom {s : ℝ} (hs1 : s < 1) {q : ℝ≥0∞} (hq : 0 < q) (m : ℕ → ℕ) :
    lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
      ENNReal.ofReal (1 / (2 * 2 ^ ((k + 1) + m (k + 1))))) < ⊤ := by
  have hρ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (s - 1) := by positivity
  have hρ1 : (2 : ℝ) ^ (s - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine lq_geom_all hq (C := (2 : ℝ) ^ (s - 1) / 2) (ρ := (2 : ℝ) ^ (s - 1))
    (by positivity) hρ0 hρ1 (fun k => ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (wreal_geom s k (m (k + 1)))

lemma hW_poly {κ : ℝ} (hκ0 : 0 ≤ κ) {q : ℝ≥0∞} (hq : 0 < q)
    (hκ : q ≠ ⊤ → 1 < κ * q.toReal) (m : ℕ → ℕ)
    (hm : ∀ r : ℕ, 1 ≤ r → (r : ℝ) ^ κ ≤ (2 : ℝ) ^ (m r)) :
    lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * 1)) *
      ENNReal.ofReal (1 / (2 * 2 ^ ((k + 1) + m (k + 1))))) < ⊤ := by
  refine lq_poly_all hq (D := 1 / 2) (κ := κ) (by norm_num) hκ0 hκ (fun k => ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (wreal_poly m hm k)

/-- **Estabilidade (Teorema 3.2) para `0 < s < 1/p`.** -/
theorem conj2_low {p s : ℝ} (hp : 1 ≤ p) (hs : s < 1 / p) {q : ℝ≥0∞} (hq : 0 < q) (c : ℝ) :
    Conj2Stability (ENNReal.ofReal p) s q (Pendencias.Agenda.Hsk (1 + 1 / p - s) 0) c := by
  intro hc 𝒩 h0 hnest hm𝒩 hcont f hf
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hs1 : s < 1 := by
    have : 1 / p ≤ 1 := by rw [div_le_one (by linarith)]; exact hp
    linarith
  refine ⟨fun hbes => ?_, fun h => stratum_subset_besov_conn hP1 𝒩 hm𝒩 s q hq hf h⟩
  exact besov_subset_stratum_low hp hs.le hq (Pendencias.Agenda.Hsk (1 + 1 / p - s) 0)
    (fun _ => 0) (hshift_low hs q (fun _ => 0) (fun _ => rfl)) (hW_geom hs1 hq (fun _ => 0))
    𝒩 h0 hnest hc hcont hf hbes

/-- **Estabilidade (Teorema 3.2) para `s = 1/p`.** -/
theorem conj2_diag {p : ℝ} (hp : 1 ≤ p) {q : ℝ≥0∞} (hq : 0 < q) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκq : p = 1 → q ≠ ⊤ → 1 < κ * q.toReal) (c : ℝ) :
    Conj2Stability (ENNReal.ofReal p) (1 / p) q
      (Pendencias.Agenda.Hsk 1 (thetaQ q + κ)) c := by
  intro hc 𝒩 h0 hnest hm𝒩 hcont f hf
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hW : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * (1 / p))) *
      ENNReal.ofReal (1 / (2 * 2 ^ ((k + 1) + mDiag κ (k + 1))))) < ⊤ := by
    rcases eq_or_lt_of_le hp with hp1 | hp1
    · have hpe : p = 1 := hp1.symm
      subst hpe
      simp only [one_div_one]
      exact hW_poly hκ0 hq (hκq rfl) (mDiag κ) (fun r hr => mDiag_ge hr)
    · have hs1 : 1 / p < 1 := by rw [div_lt_one (by linarith)]; exact hp1
      exact hW_geom hs1 hq (mDiag κ)
  refine ⟨fun hbes => ?_, fun h => stratum_subset_besov_conn hP1 𝒩 hm𝒩 (1 / p) q hq hf h⟩
  exact besov_subset_stratum_low hp le_rfl hq (Pendencias.Agenda.Hsk 1 (thetaQ q + κ))
    (mDiag κ) (hshift_diag hκ0) hW 𝒩 h0 hnest hc hcont hf hbes

/-- Nesting e demais hipóteses de `Σ^H` como família `𝒩`, para `H` monótona. -/
lemma sigma_family {H : ℕ → ℕ} (hH : Monotone H) :
    (∀ N, (0 : ℝ → ℝ) ∈ Pendencias.Agenda.Sigma H N) ∧
    (∀ N, Pendencias.Agenda.Sigma H N ⊆ Pendencias.Agenda.Sigma H (N + 1)) ∧
    (∀ N, ∀ g ∈ Pendencias.Agenda.Sigma H N, Measurable g) ∧
    (∀ N, Pendencias.Agenda.Sigma H N ⊆ Pendencias.Agenda.Sigma H ⌈(1 : ℝ) * N⌉₊) :=
  ⟨fun _ => Or.inl rfl,
   fun N => (Pendencias.Agenda.schedule_nesting hH N 0).1,
   fun _ _ hg => measurable_sigma hg,
   fun N => by rw [one_mul, Nat.ceil_natCast]⟩

/-- **Caracterização (Teorema 3.1 (ii)): `0 < s < 1/p`, todo `0 < q ≤ ∞`.** -/
theorem conj1_low {p s : ℝ} (hp : 1 ≤ p) (hs : s < 1 / p) {q : ℝ≥0∞} (hq : 0 < q) :
    ∀ f : ℝ → ℝ, Measurable f →
      (f ∈ besovP (ENNReal.ofReal p) s q ↔
        f ∈ stratumP (ENNReal.ofReal p) s q
          (Pendencias.Agenda.Sigma (Pendencias.Agenda.Hsk (1 + 1 / p - s) 0))) := by
  intro f hf
  obtain ⟨h0, hnest, hm, hcont⟩ :=
    sigma_family (Pendencias.Agenda.Hsk_mono (s := 1 + 1 / p - s) (κ := 0) le_rfl)
  exact conj2_low hp hs hq 1 le_rfl _ h0 hnest hm hcont f hf

/-- **Caracterização (Teorema 3.1 (iii)): `s = 1/p`.** -/
theorem conj1_diag {p : ℝ} (hp : 1 ≤ p) {q : ℝ≥0∞} (hq : 0 < q) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκq : p = 1 → q ≠ ⊤ → 1 < κ * q.toReal) :
    ∀ f : ℝ → ℝ, Measurable f →
      (f ∈ besovP (ENNReal.ofReal p) (1 / p) q ↔
        f ∈ stratumP (ENNReal.ofReal p) (1 / p) q
          (Pendencias.Agenda.Sigma (Pendencias.Agenda.Hsk 1 (thetaQ q + κ)))) := by
  intro f hf
  obtain ⟨h0, hnest, hm, hcont⟩ :=
    sigma_family (Pendencias.Agenda.Hsk_mono (s := 1) (κ := thetaQ q + κ)
      (add_nonneg (thetaQ_nonneg q) hκ0))
  exact conj2_diag hp hq hκ0 hκq 1 le_rfl _ h0 hnest hm hcont f hf

end FormalizacaoLow
