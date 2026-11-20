import Formalizacao.LpJackson0
import Formalizacao.Lemma52d

/-!
# M8, parte 1: dados nodais de `f`

`Q_n f(t_j) = λ_j(f)`; `λ_j` não muda se `f` muda num conjunto de medida nula; e, para `G`
contínua em `[0,1]`, `|λ_j(G)| ≤ 2B` e `|λ_{j+1}(G) - λ_j(G)| ≤ ε` para `n` grande.
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoGrid FormalizacaoL52d

namespace FormalizacaoJ

lemma Q_node {n : ℕ} (hn : 1 ≤ n) (g : ℝ → ℝ) {j : ℕ} (hj : j ≤ n) :
    Q n g (tn n j) = lam n g j := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rcases Nat.lt_or_ge j n with h | h
  · have hmem : tn n j ∈ cell n j := ⟨le_rfl, tn_mono n (Nat.le_succ j)⟩
    rw [Q_cell hn h g hmem, hat_left_of_mem hn hmem, hat_right_of_mem hn hmem, tn_succ n j hn]
    field_simp
    ring
  · have hjn : j = n := le_antisymm hj h
    subst hjn
    have hn1 : j - 1 + 1 = j := by omega
    have hk : j - 1 < j := by omega
    have hmem : tn j j ∈ cell j (j - 1) := by
      unfold cell; rw [hn1]; exact ⟨tn_mono j (Nat.sub_le j 1), le_rfl⟩
    have e := Q_cell hn hk g hmem
    rw [hat_left_of_mem hn hmem, hat_right_of_mem hn hmem, hn1] at e
    have hs := tn_succ j (j - 1) hn
    rw [hn1] at hs
    rw [e]
    have : (tn j j - tn j (j - 1)) * (j : ℝ) = 1 := by rw [hs]; field_simp; ring
    rw [sub_self, zero_mul, mul_zero, zero_add, this, mul_one]

lemma lam_congr_ae {n : ℕ} (hn : 1 ≤ n) {f G : ℝ → ℝ}
    (h : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), f x = G x) (j : ℕ) :
    lam n f j = lam n G j := by
  unfold lam
  split_ifs with hj
  · have hsub : cell n j ⊆ Icc 0 1 := cell_sub_unit hj
    have h' := ae_restrict_of_ae_restrict_of_subset hsub h
    refine integral_congr_ae ?_
    filter_upwards [h'] with y hy
    rw [hy]
  · have hsub : cell n (n - 1) ⊆ Icc 0 1 := cell_sub_unit (by omega)
    have h' := ae_restrict_of_ae_restrict_of_subset hsub h
    refine integral_congr_ae ?_
    filter_upwards [h'] with y hy
    rw [hy]

/-- cotas nodais de `G` contínua em `[0,1]` -/
lemma nodal_G {G : ℝ → ℝ} (hG : ContinuousOn G (Icc 0 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, j ≤ n → |lam n G j| ≤ 2 * B) ∧
      ∀ ε : ℝ, 0 < ε → ∃ n1 : ℕ, ∀ n : ℕ, n1 ≤ n → 2 ≤ n → ∀ j : ℕ, j < n →
        |lam n G (j + 1) - lam n G j| ≤ ε := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  refine ⟨max C 0, le_max_right _ _, ?_, ?_⟩
  · intro n hn j hj
    refine abs_lam_sup_le hn (le_max_right _ _) j hj (fun y hy => ?_)
    have hy' : y ∈ Icc (0 : ℝ) 1 := cell_sub_unit (by unfold cellIdx; omega) hy
    have := hC y hy'
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · intro ε hε
    obtain ⟨δ, hδ, hδG⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hG) (ε / 5) (by positivity)
    refine ⟨⌈1 / δ⌉₊ + 1, fun n hn1 hn2 j hj => ?_⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnδ : 1 / (n : ℝ) < δ := by
      have h1 : (⌈1 / δ⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn1
      have h2 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
      rw [div_lt_iff₀ hn0]
      have : 1 / δ < n := by linarith
      rw [div_lt_iff₀ hδ] at this
      linarith
    have hω : omega1 n G ≤ ENNReal.ofReal (ε / 5) := by
      unfold omega1
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have hd : dist x y < δ := by
        rw [Real.dist_eq]; exact lt_of_le_of_lt hxy hnδ
      have := hδG x hx y hy hd
      rw [Real.dist_eq] at this
      exact this.le
    have hd := lam_diff_le (n := n) hn2 hG hj
    have h5 : ENNReal.ofReal |lam n G (j + 1) - lam n G j| ≤ ENNReal.ofReal ε := by
      refine hd.trans ?_
      calc 5 * omega1 n G ≤ 5 * ENNReal.ofReal (ε / 5) := by gcongr
        _ = ENNReal.ofReal ε := by
          rw [show (5 : ℝ≥0∞) = ENNReal.ofReal 5 by simp, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
    exact (ENNReal.ofReal_le_ofReal_iff hε.le).1 h5

end FormalizacaoJ
