import Formalizacao.LocalError
import Formalizacao.LpDefs

/-!
# Corolário 5.4 do artigo: erro de quase-interpolação em `L^p`, a partir de Whitney (M5)

A desigualdade de Whitney em partições de `L^p` (Lema 5.3) não está demonstrada em Lean: o
Mathlib não a tem. Segue-se o plano de contingência do próprio artigo: ela entra como a
hipótese nomeada `WhitneyLp p C_W`, e o corolário é provado a partir dela, sem ocultá-la.

Com `E_k = E(f, J_k)_p = inf_a ‖f - a‖_{L^p(J_k)}` (`Ek`), a hipótese é
`(Σ_k E_k^p)^{1/p} ≤ C_W ω_p(f, 1/n)`. O corolário é
`‖f - Q_n f‖_{L^p([0,1])} ≤ 9 C_W ω_p(f, 1/n)`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace FormalizacaoCor

open FormalizacaoGrid FormalizacaoQuasi FormalizacaoLp

/-- `J_k = [t_m, t_{m+2}]`, `m = min(k, n-2)`. -/
noncomputable def Jcell (n k : ℕ) : Set ℝ :=
  Icc (tn n (min k (n - 2))) (tn n (min k (n - 2) + 2))

/-- `E(f, J_k)_p = inf_{a afim} ‖f - a‖_{L^p(J_k)}`. -/
noncomputable def Ek (p : ℝ) (f : ℝ → ℝ) (n k : ℕ) : ℝ≥0∞ :=
  ⨅ (α : ℝ) (β : ℝ), Np p (fun x => f x - (α + β * x)) (Jcell n k)

/-- **Hipótese de Whitney em partições de `L^p`** (Lema 5.3; contingência do marco M5). -/
def WhitneyLp (p CW : ℝ) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ f : ℝ → ℝ, Measurable f → IntegrableOn f (Icc 0 1) →
    Np p f (Icc 0 1) < ⊤ →
    (∑ k ∈ Finset.range n, Ek p f n k ^ p) ^ (1 / p) ≤
      ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f

/-- `[0,1]` é coberto pelas células `I_k`, `k < n`. -/
lemma unit_subset_cells {n : ℕ} (hn : 2 ≤ n) :
    Icc (0 : ℝ) 1 ⊆ ⋃ k : Fin n, cell n k := by
  intro x hx
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set k0 := ⌊x * n⌋₊ with hk0
  rw [mem_iUnion]
  by_cases hk : k0 ≤ n - 1
  · refine ⟨⟨k0, by omega⟩, ?_⟩
    have h1 : (k0 : ℝ) ≤ x * n := Nat.floor_le (by nlinarith [hx.1])
    have h2 : x * n < (k0 : ℝ) + 1 := Nat.lt_floor_add_one _
    unfold cell
    constructor
    · unfold tn
      rw [div_le_iff₀ hn']
      linarith
    · unfold tn
      push_cast
      rw [le_div_iff₀ hn']
      linarith
  · refine ⟨⟨n - 1, by omega⟩, ?_⟩
    have hx1 : x = 1 := by
      have hk2 : n ≤ k0 := by omega
      have h3 : (n : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast hk2
      have h4 : (k0 : ℝ) ≤ x * n := Nat.floor_le (by nlinarith [hx.1])
      have h5 : x * n ≤ n := by nlinarith [hx.2]
      have h6 : x * n = n := by linarith
      have h7 : x = 1 := by
        have := mul_right_cancel₀ hn'.ne' (show x * n = 1 * n by linarith)
        exact this
      exact h7
    have hn1 : n - 1 + 1 = n := by omega
    have htn : tn n n = 1 := by
      unfold tn
      field_simp
    have hlast : tn n (n - 1) + 1 / n = 1 := by
      have := tn_succ n (n - 1) (by omega)
      rw [hn1, htn] at this
      linarith
    have hpos : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    show tn n (n - 1) ≤ x ∧ x ≤ tn n (n - 1 + 1)
    rw [hn1, htn, hx1]
    constructor <;> linarith

/-- Integral de `f^p`: `(‖h‖_{L^p(S)})^p = ∫_S ‖h‖ₑ^p`. -/
lemma Np_rpow_eq {p : ℝ} (hp : 1 ≤ p) (h : ℝ → ℝ) (S : Set ℝ) :
    Np p h S ^ p = ∫⁻ x in S, ‖h x‖ₑ ^ p := by
  unfold Np
  have hp0 : (0 : ℝ) < p := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne',
    ENNReal.rpow_one]

/-- `(x^{1/p})^p = x` para `p ≥ 1`. -/
lemma rpow_inv_rpow_self {p : ℝ} (hp : 1 ≤ p) (x : ℝ≥0∞) : (x ^ (1 / p)) ^ p = x := by
  have hp0 : p ≠ 0 := by linarith
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0, ENNReal.rpow_one]

/-- Erro local com ínfimo: `‖f - Q_n f‖_{L^p(I_k)} ≤ 9 E_k`. -/
theorem local_error_inf {p : ℝ} (hp : 1 ≤ p) {n : ℕ} (hn : 2 ≤ n) {k : ℕ} (hk : k < n)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) :
    Np p (fun x => f x - Q n f x) (cell n k) ≤ 9 * Ek p f n k := by
  unfold Ek
  have h9z : (9 : ℝ≥0∞) ≠ 0 := by norm_num
  have h9t : (9 : ℝ≥0∞) ≠ ⊤ := by norm_num
  simp only [ENNReal.mul_iInf_of_ne h9z h9t]
  refine le_iInf fun α => le_iInf fun β => ?_
  exact local_error hp hn hk hf hfi hfin α β

/-- Decomposição de `‖g‖^p_{L^p([0,1])}` nas células: `‖g‖^p ≤ Σ_k ‖g‖^p_{L^p(I_k)}`. -/
theorem sum_cells_le {p : ℝ} (hp : 1 ≤ p) {n : ℕ} (hn : 2 ≤ n) (g : ℝ → ℝ) :
    Np p g (Icc 0 1) ^ p ≤ ∑ k ∈ Finset.range n, Np p g (cell n k) ^ p := by
  rw [Np_rpow_eq hp]
  calc ∫⁻ x in Icc 0 1, ‖g x‖ₑ ^ p
      ≤ ∫⁻ x in ⋃ k : Fin n, cell n k, ‖g x‖ₑ ^ p :=
        lintegral_mono' (Measure.restrict_mono (unit_subset_cells hn) le_rfl) le_rfl
    _ ≤ ∑' k : Fin n, ∫⁻ x in cell n k, ‖g x‖ₑ ^ p := lintegral_iUnion_le _ _
    _ = ∑ k : Fin n, ∫⁻ x in cell n k, ‖g x‖ₑ ^ p := tsum_fintype _
    _ = ∑ k ∈ Finset.range n, Np p g (cell n k) ^ p := by
        rw [← Fin.sum_univ_eq_sum_range (fun k => Np p g (cell n k) ^ p)]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Np_rpow_eq hp]

/-- **Corolário 5.4.** Sob a hipótese de Whitney `WhitneyLp p C_W`,
`‖f - Q_n f‖_{L^p([0,1])} ≤ 9 C_W ω_p(f, 1/n)`. -/
theorem quasi_error {p CW : ℝ} (hp : 1 ≤ p) (hW : WhitneyLp p CW) {n : ℕ} (hn : 2 ≤ n)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) :
    Np p (fun x => f x - Q n f x) (Icc 0 1) ≤
      9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f := by
  have hp0 : 0 < p := by linarith
  set Y := ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f with hY
  have hS : ∑ k ∈ Finset.range n, Ek p f n k ^ p ≤ Y ^ p := by
    have h := hW n hn f hf hfi hfin
    rw [← hY] at h
    have h2 := ENNReal.rpow_le_rpow h hp0.le
    rwa [rpow_inv_rpow_self hp] at h2
  have hcell : ∀ k ∈ Finset.range n, Np p (fun x => f x - Q n f x) (cell n k) ^ p ≤
      9 ^ p * Ek p f n k ^ p := by
    intro k hk
    have hkn : k < n := Finset.mem_range.1 hk
    have h1 := local_error_inf hp hn hkn hf hfi hfin
    have h2 := ENNReal.rpow_le_rpow h1 hp0.le
    rwa [ENNReal.mul_rpow_of_nonneg _ _ hp0.le] at h2
  have hsum := sum_cells_le hp hn (fun x => f x - Q n f x)
  have hfinal : Np p (fun x => f x - Q n f x) (Icc 0 1) ^ p ≤ (9 * Y) ^ p := by
    calc Np p (fun x => f x - Q n f x) (Icc 0 1) ^ p
        ≤ ∑ k ∈ Finset.range n, Np p (fun x => f x - Q n f x) (cell n k) ^ p := hsum
      _ ≤ ∑ k ∈ Finset.range n, 9 ^ p * Ek p f n k ^ p := Finset.sum_le_sum hcell
      _ = 9 ^ p * ∑ k ∈ Finset.range n, Ek p f n k ^ p := by rw [Finset.mul_sum]
      _ ≤ 9 ^ p * Y ^ p := mul_le_mul_left' hS _
      _ = (9 * Y) ^ p := (ENNReal.mul_rpow_of_nonneg _ _ hp0.le).symm
  have key := (ENNReal.rpow_le_rpow_iff hp0).1 hfinal
  exact key.trans (le_of_eq (by rw [hY, mul_assoc]))

end FormalizacaoCor
