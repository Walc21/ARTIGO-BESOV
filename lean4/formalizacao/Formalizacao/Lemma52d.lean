import Formalizacao.LocalError

/-!
# Lema 5.2(d): saltos dos valores nodais (M4 (d))

Para `f` contínua em `[0,1]` e `ω₁(f, 1/n)_∞` o módulo de continuidade (sup de `|f(x) - f(y)|`
sobre `x, y ∈ [0,1]` com `|x - y| ≤ 1/n`, em `[0,∞]`):

  `|λ_{j+1}(f) - λ_j(f)| ≤ 5 ω₁(f, 1/n)_∞`,   `0 ≤ j ≤ n-1`.

A prova: `λ_j(f) - f(t_j)` é o valor nodal de `f - f(t_j)` (linearidade, `lam_sub`, com `α = f(t_j)`,
`β = 0`), que é `≤ ω₁` na célula `I_{c(j)}`, onde `t_j` é extremo; pela cota `2 sup|g|` (Lema 5.2(c))
vem `|λ_j - f(t_j)| ≤ 2ω₁`. Somando os dois nós e `|f(t_{j+1}) - f(t_j)| ≤ ω₁` obtém-se `5ω₁`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace FormalizacaoL52d

open FormalizacaoGrid

/-- `ω₁(f, 1/n)_∞` em `[0,∞]`. -/
noncomputable def omega1 (n : ℕ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ Icc (0 : ℝ) 1, ⨆ y ∈ Icc (0 : ℝ) 1,
    ⨆ (_ : |x - y| ≤ 1 / (n : ℝ)), ENNReal.ofReal |f x - f y|

/-- Um ponto de `I_{c(j)}` dista no máximo `1/n` do nó `t_j`. -/
lemma cell_dist {n : ℕ} (hn : 1 ≤ n) {j : ℕ} (hj : j ≤ n) {x : ℝ}
    (hx : x ∈ cell n (cellIdx n j)) : |x - tn n j| ≤ 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := tn_succ n (cellIdx n j) hn
  unfold cell at hx
  obtain ⟨h1, h2⟩ := hx
  by_cases hjn : j < n
  · have hc : cellIdx n j = j := by unfold cellIdx; omega
    rw [hc] at h1 h2 hs
    rw [abs_le]
    constructor <;> linarith
  · have hjn' : j = n := by omega
    rw [hjn'] at h1 h2 hs ⊢
    have hc : cellIdx n n = n - 1 := by unfold cellIdx; omega
    have hn1 : n - 1 + 1 = n := by omega
    rw [hc, hn1] at h2
    rw [hc] at h1 hs
    rw [hn1] at hs
    have htn : tn n n = 1 := by unfold tn; field_simp
    rw [abs_le]
    constructor <;> linarith

/-- Cota pontual: `|f(x) - f(t_j)| ≤ ω₁` para `x` na célula de `t_j`. -/
lemma ofReal_le_omega1 {n : ℕ} (hn : 1 ≤ n) (f : ℝ → ℝ) {j : ℕ} (hj : j ≤ n) {x : ℝ}
    (hx : x ∈ cell n (cellIdx n j)) :
    ENNReal.ofReal |f x - f (tn n j)| ≤ omega1 n f := by
  have hxI : x ∈ Icc (0 : ℝ) 1 := cell_sub_unit (by unfold cellIdx; omega) hx
  have htI : tn n j ∈ Icc (0 : ℝ) 1 := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨by unfold tn; positivity, ?_⟩
    unfold tn
    rw [div_le_one hn']
    exact_mod_cast hj
  unfold omega1
  exact le_iSup₂_of_le x hxI (le_iSup₂_of_le (tn n j) htI
    (le_iSup_of_le (cell_dist hn hj hx) le_rfl))

/-- `ω₁(f, 1/n)_∞ < ∞` para `f` contínua em `[0,1]`. -/
lemma omega1_ne_top {n : ℕ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    omega1 n f ≠ ⊤ := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hle : omega1 n f ≤ ENNReal.ofReal (2 * M) := by
    unfold omega1
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun _ => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hM x hx
    have h2 := hM y hy
    rw [Real.norm_eq_abs] at h1 h2
    calc |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- **Lema 5.2(d).** Para `f` contínua em `[0,1]`, `0 ≤ j ≤ n-1`:
`|λ_{j+1}(f) - λ_j(f)| ≤ 5 ω₁(f, 1/n)_∞`. -/
theorem lam_diff_le {n : ℕ} (hn : 2 ≤ n) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    {j : ℕ} (hj : j < n) :
    ENNReal.ofReal |lam n f (j + 1) - lam n f j| ≤ 5 * omega1 n f := by
  have hn1 : 1 ≤ n := by omega
  have hfi : ∀ i, i < n → IntegrableOn f (cell n i) := fun i hi =>
    (hf.mono (cell_sub_unit hi)).integrableOn_Icc
  set W : ℝ := (omega1 n f).toReal with hWdef
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hW : ∀ i, i ≤ n → ∀ x ∈ cell n (cellIdx n i), |f x - f (tn n i)| ≤ W := fun i hi x hx =>
    (ENNReal.ofReal_le_iff_le_toReal (omega1_ne_top hf)).1 (ofReal_le_omega1 hn1 f hi hx)
  -- `|λ_i - f(t_i)| ≤ 2W`
  have key : ∀ i, i ≤ n → |lam n f i - f (tn n i)| ≤ 2 * W := by
    intro i hi
    have h := lam_sub hn1 (f (tn n i)) 0 i hi hfi
    rw [lam_affine hn1 _ 0 i hi] at h
    have hval : lam n f i - f (tn n i) = lam n (fun y => f y - (f (tn n i) + 0 * y)) i := by
      rw [h]; ring
    rw [hval]
    refine abs_lam_sup_le hn1 hW0 i hi (fun y hy => ?_)
    simp only [zero_mul, add_zero]
    exact hW i hi y hy
  -- o nó `t_{j+1}` está na célula `I_j`
  have hmem : tn n (j + 1) ∈ cell n (cellIdx n j) := by
    have hc : cellIdx n j = j := by unfold cellIdx; omega
    rw [hc]
    unfold cell
    exact ⟨tn_mono n (Nat.le_succ j), le_rfl⟩
  have hc' : |f (tn n (j + 1)) - f (tn n j)| ≤ W := hW j hj.le _ hmem
  have hD : |lam n f (j + 1) - lam n f j| ≤ 5 * W := by
    have k1 := key (j + 1) (by omega)
    have k2 := key j hj.le
    have e1 := abs_add_le (lam n f (j + 1) - f (tn n (j + 1)) - (lam n f j - f (tn n j)))
      (f (tn n (j + 1)) - f (tn n j))
    have e2 := abs_sub (lam n f (j + 1) - f (tn n (j + 1))) (lam n f j - f (tn n j))
    have e3 : lam n f (j + 1) - lam n f j =
        lam n f (j + 1) - f (tn n (j + 1)) - (lam n f j - f (tn n j))
          + (f (tn n (j + 1)) - f (tn n j)) := by ring
    rw [e3]
    linarith
  calc ENNReal.ofReal |lam n f (j + 1) - lam n f j|
      ≤ ENNReal.ofReal (5 * W) := ENNReal.ofReal_le_ofReal hD
    _ = ENNReal.ofReal 5 * ENNReal.ofReal W := ENNReal.ofReal_mul (by norm_num)
    _ = 5 * omega1 n f := by
        rw [hWdef, ENNReal.ofReal_toReal (omega1_ne_top hf)]
        simp

end FormalizacaoL52d
