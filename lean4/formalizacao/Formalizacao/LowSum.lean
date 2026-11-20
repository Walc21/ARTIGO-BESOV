import Mathlib
import Formalizacao.LpDefs

/-!
# Regimes `s ≤ 1/p`, parte 3: somas parciais de sequências de `ℓ^q`

Para `a ∈ ℓ^q` (`0 < q ≤ ∞`), as somas parciais satisfazem
`∑_{k<r} a_k ≤ r^{θ_q} ‖a‖_{ℓ^q}`, com `θ_q = max{0, 1 - 1/q}` e `θ_∞ = 1`
(Hölder para `q > 1`, inclusão `ℓ^q ⊆ ℓ^1` para `q ≤ 1`, e `q = ∞` trivial).
É a única informação sobre `ℓ^q` usada na cota em sup dos quase-interpolantes no caso `s = 1/p`.
-/

open scoped ENNReal
open FormalizacaoLp

namespace FormalizacaoLow

/-- Expoente `θ_q = max{0, 1 - 1/q}`, com `θ_∞ = 1`. -/
noncomputable def thetaQ (q : ℝ≥0∞) : ℝ := if q ≤ 1 then 0 else 1 - 1 / q.toReal

lemma thetaQ_top : thetaQ ⊤ = 1 := by simp [thetaQ]

lemma thetaQ_nonneg (q : ℝ≥0∞) : 0 ≤ thetaQ q := by
  unfold thetaQ
  split_ifs with h
  · exact le_rfl
  · by_cases hqt : q = ⊤
    · subst hqt; simp
    · have ht : 1 < q.toReal := by
        have := (ENNReal.toReal_lt_toReal (by simp) hqt).2 (not_le.1 h)
        simpa using this
      have : 1 / q.toReal ≤ 1 := by
        rw [div_le_one (by linarith)]; exact ht.le
      linarith

lemma sum_rpow_le_of_le_one {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {ι : Type*} (f : ι → ℝ) :
    ∀ s : Finset ι, (∀ i ∈ s, 0 ≤ f i) → (∑ i ∈ s, f i) ^ t ≤ ∑ i ∈ s, f i ^ t := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp [Real.zero_rpow ht0.ne']
  | insert a s ha ih =>
    intro hf
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hf' : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hs : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hf'
    calc (f a + ∑ i ∈ s, f i) ^ t ≤ f a ^ t + (∑ i ∈ s, f i) ^ t :=
          Real.rpow_add_le_add_rpow hfa hs ht0.le ht1
      _ ≤ f a ^ t + ∑ i ∈ s, f i ^ t := by gcongr; exact ih hf'

/-- **Somas parciais de `ℓ^q`.** -/
theorem sum_le_lq {q : ℝ≥0∞} (hq : 0 < q) {b : ℕ → ℝ≥0∞} (hb : lqNorm q b < ⊤) (r : ℕ) :
    ∑ k ∈ Finset.range r, (b k).toReal ≤ (r : ℝ) ^ thetaQ q * (lqNorm q b).toReal := by
  by_cases hqt : q = ⊤
  · subst hqt
    rw [thetaQ_top, Real.rpow_one]
    have hS : lqNorm ⊤ b = ⨆ k, b k := by simp [lqNorm]
    rw [hS] at hb ⊢
    have hle : ∀ k, (b k).toReal ≤ (⨆ k, b k).toReal := fun k =>
      ENNReal.toReal_mono hb.ne (le_iSup b k)
    calc ∑ k ∈ Finset.range r, (b k).toReal ≤ ∑ k ∈ Finset.range r, (⨆ k, b k).toReal :=
          Finset.sum_le_sum (fun k _ => hle k)
      _ = r * (⨆ k, b k).toReal := by simp
  · set t := q.toReal with ht
    have ht0 : 0 < t := ENNReal.toReal_pos hq.ne' hqt
    have hl : lqNorm q b = (∑' k, b k ^ t) ^ t⁻¹ := by simp [lqNorm, hqt, ht]
    set A := ∑' k, b k ^ t with hA
    have hAfin : A ≠ ⊤ := by
      rw [hl] at hb
      by_contra h
      rw [h, ENNReal.top_rpow_of_pos (inv_pos.2 ht0)] at hb
      exact lt_irrefl _ hb
    have hbk : ∀ k, b k ≠ ⊤ := by
      intro k hk
      apply hAfin
      refine top_le_iff.1 ?_
      calc (⊤ : ℝ≥0∞) = b k ^ t := by rw [hk, ENNReal.top_rpow_of_pos ht0]
        _ ≤ A := ENNReal.le_tsum k
    have hnn : ∀ k ∈ Finset.range r, 0 ≤ (b k).toReal := fun _ _ => ENNReal.toReal_nonneg
    have hsumpow : ∑ k ∈ Finset.range r, ((b k).toReal) ^ t ≤ A.toReal := by
      have h1 : ∑ k ∈ Finset.range r, (b k) ^ t ≤ A := ENNReal.sum_le_tsum _
      have h2 := ENNReal.toReal_mono hAfin h1
      rw [ENNReal.toReal_sum (fun k _ => ENNReal.rpow_ne_top_of_nonneg ht0.le (hbk k))] at h2
      simpa [ENNReal.toReal_rpow] using h2
    have hltoReal : (lqNorm q b).toReal = A.toReal ^ t⁻¹ := by rw [hl, ENNReal.toReal_rpow]
    rw [hltoReal]
    have hSnn : 0 ≤ ∑ k ∈ Finset.range r, (b k).toReal := Finset.sum_nonneg hnn
    have hrecover : ∑ k ∈ Finset.range r, (b k).toReal =
        ((∑ k ∈ Finset.range r, (b k).toReal) ^ t) ^ t⁻¹ := by
      rw [← Real.rpow_mul hSnn, mul_inv_cancel₀ ht0.ne', Real.rpow_one]
    by_cases hq1 : q ≤ 1
    · have hθ : thetaQ q = 0 := by simp [thetaQ, hq1]
      rw [hθ, Real.rpow_zero, one_mul]
      have ht1 : t ≤ 1 := by
        have := ENNReal.toReal_mono (by simp) hq1
        simpa [ht] using this
      have h1 := sum_rpow_le_of_le_one ht0 ht1 (fun k => (b k).toReal) (Finset.range r) hnn
      have h2 : (∑ k ∈ Finset.range r, (b k).toReal) ^ t ≤ A.toReal := h1.trans hsumpow
      calc ∑ k ∈ Finset.range r, (b k).toReal
          = ((∑ k ∈ Finset.range r, (b k).toReal) ^ t) ^ t⁻¹ := hrecover
        _ ≤ A.toReal ^ t⁻¹ :=
          Real.rpow_le_rpow (Real.rpow_nonneg hSnn t) h2 (inv_pos.2 ht0).le
    · have hθ : thetaQ q = 1 - 1 / t := by simp [thetaQ, hq1, ht]
      have ht1 : 1 < t := by
        have := (ENNReal.toReal_lt_toReal (by simp) hqt).2 (not_le.1 hq1)
        simpa [ht] using this
      rw [hθ]
      have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (Finset.range r)
        (f := fun k => (b k).toReal) ht1.le hnn
      simp only [Finset.card_range] at h
      have h2 : (∑ k ∈ Finset.range r, (b k).toReal) ^ t ≤ (r : ℝ) ^ (t - 1) * A.toReal :=
        h.trans (mul_le_mul_of_nonneg_left hsumpow (Real.rpow_nonneg (Nat.cast_nonneg r) _))
      calc ∑ k ∈ Finset.range r, (b k).toReal
          = ((∑ k ∈ Finset.range r, (b k).toReal) ^ t) ^ t⁻¹ := hrecover
        _ ≤ ((r : ℝ) ^ (t - 1) * A.toReal) ^ t⁻¹ :=
          Real.rpow_le_rpow (Real.rpow_nonneg hSnn t) h2 (inv_pos.2 ht0).le
        _ = (r : ℝ) ^ (1 - 1 / t) * A.toReal ^ t⁻¹ := by
          rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg r) _) ENNReal.toReal_nonneg,
            ← Real.rpow_mul (Nat.cast_nonneg r)]
          congr 2
          field_simp

end FormalizacaoLow
