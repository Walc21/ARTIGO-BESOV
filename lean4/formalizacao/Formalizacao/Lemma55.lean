import Formalizacao.Embedding
import Formalizacao.Corollary54
import Formalizacao.LpAxioms

/-!
# Lema 5.5 do artigo (M6): embedding de Besov e cota de ω₁

Passos formalizados aqui:
* `Q_affine_on_cell`: `Q_n g` é afim em cada célula grossa `I_k`;
* `cell_fine_sub_coarse`: a célula fina `I_j^{(2n)}` está em `I_{j/2}^{(n)}`;
* `Q_diff_affine_fine`: `Q_{2n} g - Q_n g` é afim em cada célula fina.
-/

open scoped ENNReal
open MeasureTheory Set

namespace FormalizacaoL55

open FormalizacaoGrid FormalizacaoQuasi FormalizacaoLp

/-- `Q_n g` é afim em cada célula `I_k`, `k < n`. -/
theorem Q_affine_on_cell {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : k < n) (g : ℝ → ℝ) :
    ∃ α β : ℝ, ∀ x ∈ cell n k, Q n g x = α + β * x := by
  have hn' : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  refine ⟨lam n g k * n * tn n (k + 1) - lam n g (k + 1) * n * tn n k,
    (lam n g (k + 1) - lam n g k) * n, fun x hx => ?_⟩
  rw [Q_cell hn hk g hx, hat_left_of_mem hn hx, hat_right_of_mem hn hx]
  have hsucc := tn_succ n k hn
  rw [hsucc]
  field_simp
  ring

/-- Célula fina `I_j^{(2n)}` contida na célula grossa `I_{j/2}^{(n)}`. -/
theorem cell_fine_sub_coarse {n j : ℕ} (hn : 1 ≤ n) (hj : j < 2 * n) :
    cell (2 * n) j ⊆ cell n (j / 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hjm : j / 2 < n := by omega
  have hA : tn n (j / 2) ≤ tn (2 * n) j := by
    unfold tn
    rw [div_le_div_iff₀ hn' (by positivity)]
    have : ((j / 2 : ℕ) : ℝ) * 2 ≤ (j : ℝ) := by
      have : (j / 2) * 2 ≤ j := Nat.div_mul_le_self j 2
      exact_mod_cast this
    push_cast
    nlinarith
  have hB : tn (2 * n) (j + 1) ≤ tn n (j / 2 + 1) := by
    unfold tn
    rw [div_le_div_iff₀ (by positivity) hn']
    have : (j : ℝ) + 1 ≤ ((j / 2 : ℕ) : ℝ) * 2 + 2 := by
      have h : j + 1 ≤ (j / 2) * 2 + 2 := by omega
      exact_mod_cast h
    push_cast
    nlinarith
  intro x hx
  exact ⟨le_trans hA hx.1, le_trans hx.2 (le_trans hB (le_refl _))⟩

/-- `Q_{2n} g - Q_n g` é afim em cada célula fina `I_j^{(2n)}`. -/
theorem Q_diff_affine_fine {n : ℕ} (hn : 1 ≤ n) {j : ℕ} (hj : j < 2 * n) (g : ℝ → ℝ) :
    ∃ α β : ℝ, ∀ x ∈ cell (2 * n) j, Q (2 * n) g x - Q n g x = α + β * x := by
  obtain ⟨a1, b1, h1⟩ := Q_affine_on_cell (by omega : 1 ≤ 2 * n) hj g
  obtain ⟨a2, b2, h2⟩ := Q_affine_on_cell hn (show j / 2 < n by omega) g
  refine ⟨a1 - a2, b1 - b2, fun x hx => ?_⟩
  have hx2 := cell_fine_sub_coarse hn hj hx
  rw [h1 x hx, h2 x hx2]
  ring

/-- Célula como intervalo fechado de comprimento `1/N`. -/
lemma cell_eq_Icc {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    cell N j = Icc (tn N j) (tn N j + 1 / N) := by
  unfold cell
  rw [tn_succ N j hN]

/-- Norma `L^p` de `v` numa célula em que `v` é afim, pela norma da afim. -/
lemma Np_eq_affine_cell {p : ℝ} {N j : ℕ} (hN : 1 ≤ N) {v : ℝ → ℝ} {α β : ℝ}
    (hv : ∀ x ∈ cell N j, v x = α + β * x) :
    Np p v (cell N j) = eLpNorm (fun y => α + β * y) (ENNReal.ofReal p)
      (volume.restrict (Icc (tn N j) (tn N j + 1 / N))) := by
  unfold Np
  rw [cell_eq_Icc hN j] at hv ⊢
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hv x hx

/-- Cotas da forma `Np`: `Np v I_j ≤ Np v [0,1]`. -/
lemma Np_cell_le {p : ℝ} {N j : ℕ} (hN : 1 ≤ N) (hj : j < N) (v : ℝ → ℝ) :
    Np p v (cell N j) ≤ Np p v (Icc 0 1) := by
  unfold Np
  exact eLpNorm_mono_measure v (Measure.restrict_mono (cell_sub_unit hj) le_rfl)

/-- **Cota de sup para funções afins por célula.** -/
theorem sup_le_of_affine_cells {p : ℝ} (hp : 1 ≤ p) {N : ℕ} (hN2 : 2 ≤ N) {v : ℝ → ℝ}
    (hv : ∀ j, j < N → ∃ α β : ℝ, ∀ x ∈ cell N j, v x = α + β * x)
    (hfin : Np p v (Icc 0 1) < ⊤) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |v x| ≤ 8 * (1 / (N : ℝ)) ^ (-(1 / p)) * (Np p v (Icc 0 1)).toReal := by
  have hN : 1 ≤ N := by omega
  obtain ⟨k, hk⟩ := mem_iUnion.1 (FormalizacaoCor.unit_subset_cells hN2 hx)
  obtain ⟨α, β, hab⟩ := hv k.1 k.2
  have hvx : v x = α + β * x := hab x hk
  rw [hvx]
  have hℓ : (0 : ℝ) < 1 / N := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hin := FormalizacaoEmb.inverse_affine_sup (a := tn N k.1) (ℓ := 1 / N) (α := α) (β := β) (p := p)
    hℓ hp (x := x) (by
      rw [← cell_eq_Icc hN k.1]
      exact hk)
  have hcell := Np_eq_affine_cell (p := p) hN (v := v) (j := k.1) (α := α) (β := β) hab
  have hbound : (eLpNorm (fun y => α + β * y) (ENNReal.ofReal p)
      (volume.restrict (Icc (tn N k.1) (tn N k.1 + 1 / N)))).toReal ≤ (Np p v (Icc 0 1)).toReal := by
    rw [← hcell]
    exact ENNReal.toReal_mono hfin.ne (Np_cell_le hN k.2 v)
  have hc : (0 : ℝ) ≤ 8 * (1 / (N : ℝ)) ^ (-(1 / p)) := by positivity
  calc |α + β * x| ≤ 8 * (1 / (N : ℝ)) ^ (-(1 / p)) * (eLpNorm (fun y => α + β * y)
        (ENNReal.ofReal p) (volume.restrict (Icc (tn N k.1) (tn N k.1 + 1 / N)))).toReal := hin
    _ ≤ 8 * (1 / (N : ℝ)) ^ (-(1 / p)) * (Np p v (Icc 0 1)).toReal :=
        mul_le_mul_of_nonneg_left hbound hc

/-- **Cota de inclinação para funções afins por célula.** -/
theorem slope_le_of_affine_cells {p : ℝ} (hp : 1 ≤ p) {N : ℕ} (hN2 : 2 ≤ N) {v : ℝ → ℝ}
    (hv : ∀ j, j < N → ∃ α β : ℝ, ∀ x ∈ cell N j, v x = α + β * x)
    (hfin : Np p v (Icc 0 1) < ⊤) {j : ℕ} (hj : j < N) :
    ∃ β : ℝ, |β| ≤ 8 * (1 / (N : ℝ)) ^ (-(1 / p) - 1) * (Np p v (Icc 0 1)).toReal ∧
      ∃ α : ℝ, ∀ x ∈ cell N j, v x = α + β * x := by
  have hN : 1 ≤ N := by omega
  obtain ⟨α, β, hab⟩ := hv j hj
  refine ⟨β, ?_, α, hab⟩
  have hℓ : (0 : ℝ) < 1 / N := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hb := FormalizacaoEmb.bernstein_affine (a := tn N j) (ℓ := 1 / N) (α := α) (β := β) (p := p) hℓ hp
  have hcell := Np_eq_affine_cell (p := p) hN (v := v) (j := j) (α := α) (β := β) hab
  have hbound : (eLpNorm (fun y => α + β * y) (ENNReal.ofReal p)
      (volume.restrict (Icc (tn N j) (tn N j + 1 / N)))).toReal ≤ (Np p v (Icc 0 1)).toReal := by
    rw [← hcell]
    exact ENNReal.toReal_mono hfin.ne (Np_cell_le hN hj v)
  have hc : (0 : ℝ) ≤ 8 * (1 / (N : ℝ)) ^ (-(1 / p) - 1) := by positivity
  calc |β| ≤ 8 * (1 / (N : ℝ)) ^ (-(1 / p) - 1) * (eLpNorm (fun y => α + β * y)
        (ENNReal.ofReal p) (volume.restrict (Icc (tn N j) (tn N j + 1 / N)))).toReal := hb
    _ ≤ 8 * (1 / (N : ℝ)) ^ (-(1 / p) - 1) * (Np p v (Icc 0 1)).toReal :=
        mul_le_mul_of_nonneg_left hbound hc

/-- `Q_n g` é contínua. -/
theorem Q_continuous (n : ℕ) (g : ℝ → ℝ) : Continuous (Q n g) := by
  unfold Q
  apply continuous_finset_sum
  intro j _
  apply Continuous.mul continuous_const
  unfold hat
  fun_prop

/-- Norma `L^p` de `v_n = Q_{2n} f - Q_n f`, pelo Corolário 5.4 em `n` e `2n`. -/
theorem v_norm_le {p CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {n : ℕ} (hn : 2 ≤ n) {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : FormalizacaoGrid.Np p f (Icc 0 1) < ⊤) :
    FormalizacaoGrid.Np p (fun x => Q (2 * n) f x - Q n f x) (Icc 0 1) ≤
      18 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f := by
  have h1 := FormalizacaoCor.quasi_error hp hW hn hf hfi hfin
  have h2 := FormalizacaoCor.quasi_error hp hW (show 2 ≤ 2 * n by omega) hf hfi hfin
  have hmono : wtP (ENNReal.ofReal p) (1 / ((2 * n : ℕ) : ℝ)) f ≤ wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f :=
    wtP_mono_t _ f (by
      have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      push_cast
      exact one_div_le_one_div_of_le (by positivity) (by linarith))
  have hfun : (fun x => Q (2 * n) f x - Q n f x) =
      (fun x => (f x - Q n f x) + -(f x - Q (2 * n) f x)) := by
    funext x; ring
  rw [hfun]
  have hm1 : Measurable fun x => f x - Q n f x :=
    hf.sub (Q_continuous n f).measurable
  have hm2 : Measurable fun x => f x - Q (2 * n) f x :=
    hf.sub (Q_continuous (2 * n) f).measurable
  unfold FormalizacaoGrid.Np at *
  calc eLpNorm (fun x => (f x - Q n f x) + -(f x - Q (2 * n) f x)) (ENNReal.ofReal p)
        (volume.restrict (Icc 0 1))
      ≤ eLpNorm (fun x => f x - Q n f x) (ENNReal.ofReal p) (volume.restrict (Icc 0 1)) +
          eLpNorm (fun x => -(f x - Q (2 * n) f x)) (ENNReal.ofReal p) (volume.restrict (Icc 0 1)) :=
        eLpNorm_add_le hm1.aestronglyMeasurable hm2.neg.aestronglyMeasurable
          (ENNReal.one_le_ofReal.2 hp)
    _ = eLpNorm (fun x => f x - Q n f x) (ENNReal.ofReal p) (volume.restrict (Icc 0 1)) +
          eLpNorm (fun x => f x - Q (2 * n) f x) (ENNReal.ofReal p) (volume.restrict (Icc 0 1)) := by
        congr 1
        exact eLpNorm_neg (fun x => f x - Q (2 * n) f x) _ _
    _ ≤ 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f +
          9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / ((2 * n : ℕ) : ℝ)) f :=
        add_le_add h1 h2
    _ ≤ 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f +
          9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f := by
        gcongr
    _ = 18 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f := by ring

end FormalizacaoL55
