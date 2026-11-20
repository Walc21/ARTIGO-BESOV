import Formalizacao.Whitney9

/-!
# Whitney em `L^p` (M5), parte 10: a cota por célula
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoGrid

namespace FormalizacaoW

open FormalizacaoCor FormalizacaoLp

/-- `δ = 1/(4n)` -/
noncomputable def dl (n : ℕ) : ℝ := 1 / (4 * (n : ℝ))

/-- `I_k = [t_m + δ, t_m + 7δ]`, `m = min(k, n-2)` -/
noncomputable def Iset (n k : ℕ) : Set ℝ :=
  Icc (tn n (min k (n - 2)) + dl n) (tn n (min k (n - 2)) + 7 * dl n)

lemma dl_pos {n : ℕ} (hn : 1 ≤ n) : 0 < dl n := by
  unfold dl
  have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  positivity

lemma tn_n {n : ℕ} (hn : 1 ≤ n) : tn n n = 1 := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold tn; field_simp

lemma tn_zero_le (n j : ℕ) : 0 ≤ tn n j := by unfold tn; positivity

/-- `J_k = [a, a + 8δ]` com `a = t_m` -/
lemma Jcell_eq {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    Jcell n k = Icc (tn n (min k (n - 2))) (tn n (min k (n - 2)) + 8 * dl n) := by
  unfold Jcell
  congr 1
  have h1 := tn_succ n (min k (n - 2)) (by omega)
  have h2 := tn_succ n (min k (n - 2) + 1) (by omega)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have : 8 * dl n = 2 / (n : ℝ) := by unfold dl; field_simp; ring
  rw [this]
  have e : tn n (min k (n - 2) + 2) = tn n (min k (n - 2) + 1 + 1) := rfl
  rw [e, h2, h1]; ring

lemma Jcell_sub_unit {n : ℕ} (hn : 2 ≤ n) (k : ℕ) : Jcell n k ⊆ Icc 0 1 := by
  intro x hx
  unfold Jcell at hx
  have hm : min k (n - 2) + 2 ≤ n := by omega
  refine ⟨le_trans (tn_zero_le n _) hx.1, hx.2.trans ?_⟩
  calc tn n (min k (n - 2) + 2) ≤ tn n n := tn_mono n hm
    _ = 1 := tn_n (by omega)

lemma Iset_sub_J {n : ℕ} (hn : 2 ≤ n) (k : ℕ) : Iset n k ⊆ Jcell n k := by
  rw [Jcell_eq hn]
  have := dl_pos (n := n) (by omega)
  exact Icc_subset_Icc (by linarith) (by linarith)

/-- `I_k ⊆ [ρ, 1-ρ]` para `ρ ≤ δ` -/
lemma Iset_sub_rho {n : ℕ} (hn : 2 ≤ n) (k : ℕ) {ρ : ℝ} (hρ : ρ ≤ dl n) :
    Iset n k ⊆ Icc ρ (1 - ρ) := by
  intro x hx
  have hd := dl_pos (n := n) (by omega)
  have hJ := Jcell_sub_unit hn k (Iset_sub_J hn k hx)
  have hJ' := Iset_sub_J hn k hx
  rw [Jcell_eq hn] at hJ'
  have ha : 0 ≤ tn n (min k (n - 2)) := tn_zero_le n _
  have hb : tn n (min k (n - 2)) + 8 * dl n ≤ 1 := by
    have := Jcell_sub_unit hn k
    have hr : tn n (min k (n - 2)) + 8 * dl n ∈ Jcell n k := by
      rw [Jcell_eq hn]; exact ⟨by linarith, le_rfl⟩
    exact (this hr).2
  refine ⟨?_, ?_⟩
  · linarith [hx.1]
  · linarith [hx.2]

/-- **Cota por célula.** `E(f,J_k)_p^p ≤ K₁ T_k + K₂ c₀ F_k`. -/
theorem Ek_bound {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ}
    (hfm : Measurable f) (hfi : IntegrableOn f (Icc 0 1)) (k : ℕ) :
    Ek p f n k ^ p ≤ K1 p * (∫⁻ x in Iset n k, ‖Wt f x (dl n)‖ₑ ^ p) +
      K2 p * (ENNReal.ofReal ((1 / (2 * (dl n) ^ 2)) ^ p * (dl n) ^ (2 * (p - 1))) *
        ∫⁻ s in Ioc 0 (dl n), ∫⁻ r in Ioc 0 (dl n), ∫⁻ x in Iset n k, Fw f (dl n) p x s r) := by
  have hd := dl_pos (n := n) (by omega)
  have hJ : Jcell n k = Icc (tn n (min k (n - 2))) (tn n (min k (n - 2)) + 8 * dl n) :=
    Jcell_eq hn k
  have hfJ : IntegrableOn f (Icc (tn n (min k (n - 2))) (tn n (min k (n - 2)) + 8 * dl n)) := by
    rw [← hJ]; exact hfi.mono_set (Jcell_sub_unit hn k)
  obtain ⟨α, β, hab⟩ := local_whitney hp hfJ hfm hd
  have hE : Ek p f n k ≤ Np p (fun x => f x - (α + β * x)) (Jcell n k) := by
    unfold Ek
    exact iInf₂_le (f := fun (α β : ℝ) => Np p (fun x => f x - (α + β * x)) (Jcell n k)) α β
  have h2 : Ek p f n k ^ p ≤ ∫⁻ x in Jcell n k, ‖f x - (α + β * x)‖ₑ ^ p := by
    rw [← FormalizacaoCor.Np_rpow_eq hp]
    exact ENNReal.rpow_le_rpow hE (by linarith)
  rw [hJ] at h2
  refine h2.trans (le_of_eq_of_le rfl ?_)
  exact hab

end FormalizacaoW
