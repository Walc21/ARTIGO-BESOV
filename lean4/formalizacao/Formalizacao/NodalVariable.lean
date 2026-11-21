import Formalizacao.LowNodal
import Formalizacao.AlturaTerminal

/-!
# Quantização com denominadores diádicos por nó

Formalização de `lp:lem:nodal-variable-height`. Os nós pares são arredondados primeiro.
Cada nó ímpar pode então evitar os dois valores vizinhos na sua própria grade.
-/

open Artigo MeasureTheory Set
open scoped ENNReal

namespace FormalizacaoAltura

private lemma exists_dyadic_grid {w : ℝ} {H : ℕ} (hw : 0 < w) (hH : 8 * w ≤ H) :
    ∃ e : ℕ, 8 * w * (2 : ℝ) ^ e ≤ H ∧ (H : ℝ) < 16 * w * (2 : ℝ) ^ e := by
  have hw8 : 0 < 8 * w := by positivity
  have hx : 1 ≤ (H : ℝ) / (8 * w) := (one_le_div hw8).2 hH
  obtain ⟨e, he, he'⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  refine ⟨e, ?_, ?_⟩
  · linarith [(le_div_iff₀ hw8).1 he]
  · rw [div_lt_iff₀ hw8, pow_succ] at he'
    linarith

private lemma exists_grid_rounding (y : ℕ → ℝ) (e : ℕ → ℕ) :
    ∃ b : ℕ → ℤ,
      (∀ j, |y j - (b j : ℝ) / (2 : ℝ) ^ e j| ≤ 2 / (2 : ℝ) ^ e j) ∧
      (∀ j, (b j : ℚ) / (2 : ℚ) ^ e j ≠ (b (j + 1) : ℚ) / (2 : ℚ) ^ e (j + 1)) := by
  let a (j : ℕ) := round (y j * (2 : ℝ) ^ e j)
  let v (j : ℕ) (k : ℤ) : ℚ := (k : ℚ) / (2 : ℚ) ^ e j
  have hinj (j : ℕ) : Function.Injective (v j) := by
    intro k l h
    change (k : ℚ) / (2 : ℚ) ^ e j = (l : ℚ) / (2 : ℚ) ^ e j at h
    exact_mod_cast (div_left_inj' (by positivity : (2 : ℚ) ^ e j ≠ 0)).mp h
  have hchoose (j : ℕ) : ∃ k : ℤ, |k - a j| ≤ 1 ∧
      v j k ≠ v (j - 1) (a (j - 1)) ∧ v j k ≠ v (j + 1) (a (j + 1)) := by
    let A := v (j - 1) (a (j - 1))
    let B := v (j + 1) (a (j + 1))
    by_cases h₀ : v j (a j) ≠ A ∧ v j (a j) ≠ B
    · exact ⟨a j, by simp, h₀⟩
    by_cases h₁ : v j (a j - 1) ≠ A ∧ v j (a j - 1) ≠ B
    · exact ⟨a j - 1, by rw [abs_le]; omega, h₁⟩
    refine ⟨a j + 1, by rw [abs_le]; omega, ?_⟩
    have h01 : v j (a j) ≠ v j (a j - 1) := fun h ↦ by have := hinj j h; omega
    have h02 : v j (a j) ≠ v j (a j + 1) := fun h ↦ by have := hinj j h; omega
    have h12 : v j (a j - 1) ≠ v j (a j + 1) := fun h ↦ by have := hinj j h; omega
    change v j (a j + 1) ≠ A ∧ v j (a j + 1) ≠ B
    have h₀' : v j (a j) = A ∨ v j (a j) = B := by tauto
    have h₁' : v j (a j - 1) = A ∨ v j (a j - 1) = B := by tauto
    rcases h₀' with h₀' | h₀' <;> rcases h₁' with h₁' | h₁' <;> grind
  classical
  choose k hk using hchoose
  let b (j : ℕ) := if j % 2 = 0 then a j else k j
  refine ⟨b, ?_, ?_⟩
  · intro j
    have hb : |b j - a j| ≤ 1 := by
      dsimp [b]
      split_ifs
      · simp
      · exact (hk j).1
    have hb' : |(b j : ℝ) - a j| ≤ 1 := by exact_mod_cast hb
    have ha := abs_sub_round (y j * (2 : ℝ) ^ e j)
    have he : (0 : ℝ) < (2 : ℝ) ^ e j := by positivity
    rw [← mul_div_cancel_right₀ (y j) he.ne', ← sub_div, abs_div, abs_of_pos he]
    apply div_le_div_of_nonneg_right _ he.le
    calc |y j * (2 : ℝ) ^ e j - (b j : ℝ)|
        ≤ |y j * (2 : ℝ) ^ e j - (a j : ℝ)| + |(b j : ℝ) - a j| := by
              simpa only [abs_sub_comm (a j : ℝ) (b j : ℝ)] using
                abs_sub_le (y j * (2 : ℝ) ^ e j) (a j : ℝ) (b j : ℝ)
      _ ≤ 2 := by change |y j * (2 : ℝ) ^ e j - (a j : ℝ)| ≤ 1 / 2 at ha; linarith
  · intro j
    change v j (b j) ≠ v (j + 1) (b (j + 1))
    by_cases hj : j % 2 = 0
    · have hs : (j + 1) % 2 ≠ 0 := by omega
      simpa [b, hj, hs] using (hk (j + 1)).2.1.symm
    · have hs : (j + 1) % 2 = 0 := by omega
      simpa [b, hj, hs] using (hk j).2.2

private lemma lift_grid (b : ℤ) {e E : ℕ} (he : e ≤ E) :
    (b : ℚ) / (2 : ℚ) ^ e = ((b * 2 ^ (E - e) : ℤ) : ℚ) / (2 : ℚ) ^ E := by
  have hE : E = e + (E - e) := by omega
  push_cast
  rw [show (2 : ℚ) ^ E = 2 ^ e * 2 ^ (E - e) by rw [← pow_add, ← hE]]
  field_simp

private lemma variable_atom_height {V : ℤ → ℚ} {r E H : ℕ} {j b c : ℤ} {J w : ℝ}
    (hne : V j ≠ V (j + 1))
    (hb : V j = (b : ℚ) / (2 : ℚ) ^ E) (hc : V (j + 1) = (c : ℚ) / (2 : ℚ) ^ E)
    (hw : 1 ≤ w) (hD : 8 * w * (2 : ℝ) ^ E ≤ H)
    (hb' : |(b : ℝ)| ≤ 3 * (2 : ℝ) ^ E * w)
    (hc' : |(c : ℝ)| ≤ 3 * (2 : ℝ) ^ E * w)
    (hjump : |((V (j + 1) : ℚ) : ℝ) - V j| ≤ J + 4)
    (hH : (2 : ℝ) ^ r * (J + 4) ≤ H) (hH2 : 2 ≤ H) (hr : r + 1 ≤ H)
    (hj : j.natAbs + 1 ≤ H) :
    (interpAtom V r j).height ≤ H := by
  have hpow : (1 : ℝ) ≤ 2 ^ E := one_le_pow₀ (by norm_num)
  have hden : (2 : ℝ) * 2 ^ E ≤ H := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) (show (0 : ℝ) ≤ 2 ^ E by positivity)]
  have hnum : |(b : ℝ)| + |(c : ℝ)| ≤ H := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ w by linarith) (show (0 : ℝ) ≤ 2 ^ E by positivity)]
  rw [Atom.height_le_iff]
  simp only [interpAtom_k, interpAtom_m]
  refine ⟨hH2, hr, hj, ?_, ?_⟩
  · have heq : (interpAtom V r j).y0 = ((b + c : ℤ) : ℚ) / ((2 * 2 ^ E : ℕ) : ℚ) := by
      simp only [interpAtom, dif_pos hne, Atom.ofEndpoints]
      rw [hb, hc]
      push_cast
      ring
    rw [heq]
    apply Pendencias.Jackson.ht_div_le_nat _ _ (by positivity)
    · push_cast
      exact (abs_add_le _ _).trans hnum
    · exact_mod_cast hden
  · have hs : (interpAtom V r j).s = (2 : ℚ) ^ r * (V (j + 1) - V j) := by
      simp only [interpAtom, dif_pos hne, Atom.ofEndpoints]
    by_cases h : r ≤ E
    · have heq : (interpAtom V r j).s = ((c - b : ℤ) : ℚ) / ((2 ^ (E - r) : ℕ) : ℚ) := by
        rw [hs, hb, hc]
        push_cast
        rw [show (2 : ℚ) ^ E = 2 ^ r * 2 ^ (E - r) by rw [← pow_add]; congr 1; omega]
        field_simp
      rw [heq]
      apply Pendencias.Jackson.ht_div_le_nat _ _ (by positivity)
      · push_cast
        exact (abs_sub (c : ℝ) b).trans (by linarith)
      · have hmono : (2 : ℝ) ^ (E - r) ≤ 2 ^ E :=
          pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
        exact_mod_cast (show (2 : ℝ) ^ (E - r) ≤ H by linarith)
    · let d : ℤ := 2 ^ (r - E) * (c - b)
      have hd : (interpAtom V r j).s = (d : ℚ) := by
        rw [hs, hb, hc]
        dsimp [d]
        push_cast
        rw [show (2 : ℚ) ^ r = 2 ^ E * 2 ^ (r - E) by rw [← pow_add]; congr 1; omega]
        field_simp
      have hdR : (d : ℝ) = (2 : ℝ) ^ r * (((V (j + 1) : ℚ) : ℝ) - V j) := by
        exact_mod_cast hd.symm.trans hs
      rw [hd, ← div_one (d : ℚ)]
      exact Pendencias.Jackson.ht_div_le_nat d 1 (by decide) (by
        rw [hdR, abs_mul, abs_of_pos (by positivity)]
        exact (mul_le_mul_of_nonneg_left hjump (by positivity)).trans hH) (by omega)


private lemma interpAtom_mem_uniformTree (V : ℤ → ℚ) (r k : ℕ) (m j : ℤ)
    (hl : 2 ^ r * m ≤ j) (hr : j < 2 ^ r * (m + 1)) :
    interpAtom V (k + r) j ∈ (uniformTree V r k m).leaves := by
  induction r generalizing k m with
  | zero =>
    have hj : j = m := by simp at hl hr; omega
    subst j
    simp [uniformTree, LTree.leaves]
  | succ r ih =>
    simp only [uniformTree, LTree.leaves, List.mem_append]
    rw [show k + (r + 1) = k + 1 + r by omega]
    rw [pow_succ] at hl hr
    by_cases h : j < (2 : ℤ) ^ r * (2 * m + 1)
    · exact Or.inl (ih _ _ (by nlinarith) h)
    · exact Or.inr (ih _ _ (le_of_not_gt h) (by nlinarith))

private lemma nodal_cell_eq (r j : ℕ) :
    cellIcc r (j : ℤ) = FormalizacaoGrid.cell (2 ^ r) j := by
  rw [cellIcc_eq, cR_eq_cL_succ]
  simp [FormalizacaoGrid.cell, FormalizacaoGrid.tn, cL]

open FormalizacaoGrid FormalizacaoLp

/-- Em cada célula, a integral da interpolação dos módulos é a média dos extremos
multiplicada pelo comprimento da célula. -/
private lemma cell_nodal_error {n j : ℕ} (hn : 1 ≤ n) {u g : ℝ → ℝ} {a b : ℝ}
    (h : ∀ x ∈ cell n j, |u x - g x| ≤
      (1 - (n : ℝ) * (x - tn n j)) * a + (n : ℝ) * (x - tn n j) * b) :
    eLpNorm (fun x ↦ u x - g x) 1 (volume.restrict (cell n j)) ≤
      ENNReal.ofReal ((a + b) / (2 * n)) := by
  let L := tn n j
  let R := tn n (j + 1)
  let A : ℝ → ℝ := fun x ↦ (1 - (n : ℝ) * (x - L)) * a + (n : ℝ) * (x - L) * b
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hR : R = L + 1 / (n : ℝ) := tn_succ n j hn
  have hLR : L ≤ R := by rw [hR]; exact le_add_of_nonneg_right (by positivity)
  have hcont : Continuous A := by dsimp [A]; fun_prop
  rw [eLpNorm_one_eq_lintegral_enorm]
  calc
    _ ≤ ∫⁻ x in cell n j, ENNReal.ofReal (A x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (show MeasurableSet (cell n j) from measurableSet_Icc)]
        with x hx
      rw [← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal (h x hx)
    _ = ENNReal.ofReal ((a + b) / (2 * n)) := by
      have hi : IntegrableOn A (cell n j) := hcont.integrableOn_Icc
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (by
          filter_upwards [ae_restrict_mem (show MeasurableSet (cell n j) from measurableSet_Icc)]
            with x hx
          exact (abs_nonneg _).trans (h x hx))]
      congr 1
      change (∫ x in Icc L R, A x) = _
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hLR]
      have hA : A = fun x ↦ (a + (n : ℝ) * L * (a - b)) + ((n : ℝ) * (b - a)) * x := by
        funext x
        dsimp [A]
        ring
      rw [hA, intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
        ((show Continuous (fun x : ℝ ↦ (n : ℝ) * (b - a) * x) by fun_prop).intervalIntegrable _ _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
        smul_eq_mul, hR]
      field_simp
      ring

private lemma sum_adjacent_le {d : ℕ → ℝ} (hd : ∀ j, 0 ≤ d j) (n : ℕ) :
    (∑ j ∈ Finset.range n, (d j + d (j + 1))) ≤
      2 * ∑ j ∈ Finset.range (n + 1), d j := by
  rw [Finset.sum_add_distrib]
  have h₁ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ n))
    (fun j _ _ ↦ hd j)
  have h₂ : (∑ j ∈ Finset.range n, d (j + 1)) ≤ ∑ j ∈ Finset.range (n + 1), d j := by
    rw [Finset.sum_range_succ']
    linarith [hd 0]
  linarith

private lemma nodal_error_le {r : ℕ} (hr : 1 ≤ r) {y : ℕ → ℝ} {u : ℝ → ℝ} {V : ℤ → ℚ}
    (hV : GoodVals V r 0)
    (hu : ∀ j < 2 ^ r, ∀ x ∈ cell (2 ^ r) j,
      u x = (1 - (2 : ℝ) ^ r * (x - tn (2 ^ r) j)) * y j +
        (2 : ℝ) ^ r * (x - tn (2 ^ r) j) * y (j + 1)) :
    distP 1 u ((uniformTree V r 0 0).eval 0 0) ≤
      ENNReal.ofReal ((∑ j ∈ Finset.range (2 ^ r + 1), |y j - (V (j : ℤ) : ℝ)|) / (2 : ℝ) ^ r) := by
  let n : ℕ := 2 ^ r
  let g := (uniformTree V r 0 0).eval 0 0
  let d (j : ℕ) := |y j - (V (j : ℤ) : ℝ)|
  have hn : 2 ≤ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ n := Nat.pow_le_pow_right (by decide) hr
  have hcast : (n : ℝ) = (2 : ℝ) ^ r := by simp [n]
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  change distP 1 u g ≤ ENNReal.ofReal ((∑ j ∈ Finset.range (n + 1), d j) / (2 : ℝ) ^ r)
  rw [← hcast]
  have hlocal : ∀ j < n, eLpNorm (fun x ↦ u x - g x) 1 (volume.restrict (cell n j)) ≤
      ENNReal.ofReal ((d j + d (j + 1)) / (2 * n)) := by
    intro j hj
    apply cell_nodal_error (by omega)
    intro x hx
    have hx' : x ∈ cellIcc r (j : ℤ) := nodal_cell_eq r j ▸ hx
    have h₀ : (2 : ℤ) ^ r * 0 ≤ (j : ℤ) := by simp
    have h₁ : (j : ℤ) < (2 : ℤ) ^ r * (0 + 1) := by
      simp only [zero_add, mul_one]
      exact_mod_cast hj
    have hmem := interpAtom_mem_uniformTree V r 0 0 (j : ℤ) h₀ h₁
    simp only [zero_add] at hmem
    have hg := LTree.eval_leaf (uniformTree_WF V r 0 0 hV) _ hmem x (by simpa using hx')
    change g x = _ at hg
    rw [interpAtom_eval (hV j h₀ h₁)] at hg
    have hl : cL r (j : ℤ) = tn n j := by simp [cL, tn, hcast]
    rw [hcast, hu j hj x hx, hg, hl]
    have hθ := theta_mem hx'
    rw [hl] at hθ
    dsimp [d]
    let t := (2 : ℝ) ^ r * (x - tn n j)
    change |(1 - t) * y j + t * y (j + 1) -
        ((1 - t) * (V (j : ℤ) : ℝ) + t * (V ((j : ℤ) + 1) : ℝ))| ≤
        (1 - t) * |y j - (V (j : ℤ) : ℝ)| + t * |y (j + 1) - (V ((j : ℤ) + 1) : ℝ)|
    rw [show (1 - t) * y j + t * y (j + 1) -
        ((1 - t) * (V (j : ℤ) : ℝ) + t * (V ((j : ℤ) + 1) : ℝ)) =
        (1 - t) * (y j - (V (j : ℤ) : ℝ)) +
          t * (y (j + 1) - (V ((j : ℤ) + 1) : ℝ)) by ring]
    have ht0 : 0 ≤ t := hθ.1
    have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr hθ.2
    simpa only [abs_mul, abs_of_nonneg ht1, abs_of_nonneg ht0] using
      abs_add_le ((1 - t) * (y j - (V (j : ℤ) : ℝ))) (t * (y (j + 1) - (V ((j : ℤ) + 1) : ℝ)))
  have hs := FormalizacaoCor.sum_cells_le (p := 1) (by norm_num) hn (fun x ↦ u x - g x)
  simp only [Np, ENNReal.ofReal_one, ENNReal.rpow_one] at hs
  refine hs.trans (le_trans (Finset.sum_le_sum fun j hj ↦ hlocal j (Finset.mem_range.mp hj)) ?_)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by dsimp [d]; positivity), ← Finset.sum_div]
  exact ENNReal.ofReal_le_ofReal (by
    rw [div_le_div_iff₀ (by positivity) hn']
    have h := mul_le_mul_of_nonneg_right (sum_adjacent_le (d := d) (fun _ ↦ abs_nonneg _) n) hn'.le
    nlinarith)


private lemma numerator_le {v : ℚ} {b : ℤ} {E : ℕ} {y w : ℝ} (hw : 1 ≤ w)
    (hv : v = (b : ℚ) / (2 : ℚ) ^ E) (hy : |y| ≤ w) (he : |y - (v : ℝ)| ≤ 2) :
    |(b : ℝ)| ≤ 3 * (2 : ℝ) ^ E * w := by
  have hv' : (v : ℝ) = (b : ℝ) / (2 : ℝ) ^ E := by exact_mod_cast hv
  have hb : |(v : ℝ)| ≤ 3 * w := by
    calc |(v : ℝ)| ≤ |(v : ℝ) - y| + |y| := by
          simpa using (abs_add_le ((v : ℝ) - y) y)
      _ ≤ 3 * w := by rw [abs_sub_comm]; linarith
  have hE : (0 : ℝ) < (2 : ℝ) ^ E := by positivity
  rw [hv', abs_div, abs_of_pos hE, div_le_iff₀ hE] at hb
  linarith

/-- Quantização de `lp:lem:nodal-variable-height`, com as duas condições de altura do manuscrito.
A hipótese sobre `u` identifica o interpolante dos dados em cada célula fechada. -/
theorem nodal_variable_height {r H : ℕ} (hr : 1 ≤ r) {J : ℝ} (hJ : 0 ≤ J)
    (y : ℕ → ℝ) (hjump : ∀ j < 2 ^ r, |y (j + 1) - y j| ≤ J)
    (hHnode : ∀ j ≤ 2 ^ r, 8 * (1 + J + |y j|) ≤ (H : ℝ))
    (hHjump : (2 : ℝ) ^ r * (J + 4) ≤ (H : ℝ))
    (u : ℝ → ℝ)
    (hu : ∀ j < 2 ^ r, ∀ x ∈ cell (2 ^ r) j,
      u x = (1 - (2 : ℝ) ^ r * (x - tn (2 ^ r) j)) * y j +
        (2 : ℝ) ^ r * (x - tn (2 ^ r) j) * y (j + 1)) :
    ∃ g ∈ classNH (2 ^ r) H, ContinuousOn g (Icc 0 1) ∧
      distP 1 u g ≤ ENNReal.ofReal
        (32 / ((H : ℝ) * (2 : ℝ) ^ r) * ∑ j ∈ Finset.range (2 ^ r + 1), (1 + J + |y j|)) := by
  let w (j : ℕ) := 1 + J + |y j|
  have hw (j : ℕ) : 1 ≤ w j := by dsimp [w]; linarith [abs_nonneg (y j)]
  have hHpos : (0 : ℝ) < H := by linarith [hHnode 0 (Nat.zero_le _), hw 0]
  have hgrid (j : ℕ) : ∃ e : ℕ, j ≤ 2 ^ r →
      8 * w j * (2 : ℝ) ^ e ≤ H ∧ (H : ℝ) < 16 * w j * (2 : ℝ) ^ e := by
    by_cases hj : j ≤ 2 ^ r
    · obtain ⟨e, h₁, h₂⟩ := exists_dyadic_grid (show 0 < w j by linarith [hw j]) (hHnode j hj)
      exact ⟨e, fun _ ↦ ⟨h₁, h₂⟩⟩
    · exact ⟨0, fun h ↦ (hj h).elim⟩
  choose e he using hgrid
  obtain ⟨a, ha, hane⟩ := exists_grid_rounding y e
  let V (j : ℤ) : ℚ := (a j.toNat : ℚ) / (2 : ℚ) ^ e j.toNat
  have hVeq (j : ℕ) : V (j : ℤ) = (a j : ℚ) / (2 : ℚ) ^ e j := by simp [V]
  have hVerr (j : ℕ) : |y j - (V (j : ℤ) : ℝ)| ≤ 2 / (2 : ℝ) ^ e j := by
    rw [hVeq]; push_cast; exact ha j
  have hVerr2 (j : ℕ) : |y j - (V (j : ℤ) : ℝ)| ≤ 2 := by
    refine (hVerr j).trans ?_
    rw [div_le_iff₀ (by positivity)]
    linarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := e j)]
  have hV : GoodVals V r 0 := by
    intro j h₀ _
    have hj : 0 ≤ j := by simpa using h₀
    have heq : (j + 1).toNat = j.toNat + 1 := by omega
    simpa only [V, heq] using hane j.toNat
  have hnH : 2 ^ r ≤ H := by
    have h : (2 : ℝ) ^ r ≤ H := by
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) r]
    exact_mod_cast h
  have hn2 : 2 ≤ (2 : ℕ) ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) hr
  let T := uniformTree V r 0 0
  have hWF := uniformTree_WF V r 0 0 hV
  have hheight : T.maxHeight ≤ H := by
    rw [LTree.maxHeight_le_iff]
    intro A hA
    obtain ⟨j, hl, hj, rfl⟩ := uniformTree_leaves V r 0 0 A hA
    simp only [zero_add, mul_zero, mul_one] at hl hj ⊢
    lift j to ℕ using hl
    have hj' : j < (2 : ℕ) ^ r := by exact_mod_cast hj
    have hsucc : ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) := by push_cast; rfl
    let E := max (e j) (e (j + 1))
    let W := min (w j) (w (j + 1))
    let b := a j * (2 : ℤ) ^ (E - e j)
    let c := a (j + 1) * (2 : ℤ) ^ (E - e (j + 1))
    have hb : V (j : ℤ) = (b : ℚ) / (2 : ℚ) ^ E :=
      (hVeq j).trans (lift_grid _ (le_max_left _ _))
    have hc : V ((j : ℤ) + 1) = (c : ℚ) / (2 : ℚ) ^ E :=
      (congrArg V hsucc).trans ((hVeq (j + 1)).trans (lift_grid _ (le_max_right _ _)))
    have hW : 1 ≤ W := le_min (hw j) (hw (j + 1))
    have hD : 8 * W * (2 : ℝ) ^ E ≤ H := by
      rcases le_total (e j) (e (j + 1)) with h | h
      · rw [show E = e (j + 1) from max_eq_right h]
        exact le_trans (by gcongr; exact min_le_right _ _) (he (j + 1) hj').1
      · rw [show E = e j from max_eq_left h]
        exact le_trans (by gcongr; exact min_le_left _ _) (he j hj'.le).1
    have hd := hjump j hj'
    have hy₀ : |y j| ≤ W := by
      apply le_min
      · dsimp [w]; linarith
      · have h := abs_sub_le (y j) (y (j + 1)) 0
        rw [sub_zero, sub_zero, abs_sub_comm (y j)] at h
        dsimp [w]
        linarith
    have hy₁ : |y (j + 1)| ≤ W := by
      apply le_min
      · have h := abs_sub_le (y (j + 1)) (y j) 0
        simp only [sub_zero] at h
        dsimp [w]
        linarith
      · dsimp [w]; linarith
    have hs : |((V ((j : ℤ) + 1) : ℚ) : ℝ) - V (j : ℤ)| ≤ J + 4 := by
      rw [hsucc]
      have h₀ := abs_sub_le (V ((j + 1 : ℕ) : ℤ) : ℝ) (y (j + 1)) (V (j : ℤ) : ℝ)
      have h₁ := abs_sub_le (y (j + 1)) (y j) (V (j : ℤ) : ℝ)
      rw [abs_sub_comm (V ((j + 1 : ℕ) : ℤ) : ℝ) (y (j + 1))] at h₀
      linarith [hVerr2 j, hVerr2 (j + 1)]
    refine variable_atom_height (hV _ (by simp) (by simpa using hj)) hb hc hW hD
      (numerator_le hW hb hy₀ (hVerr2 j)) (numerator_le hW hc hy₁ (by rw [hsucc]; exact hVerr2 _))
      hs hHjump (hn2.trans hnH) ((Nat.lt_two_pow_self (n := r)).trans_le hnH) ?_
    simpa using (show j + 1 ≤ H from hj'.trans_le hnH)
  let g := T.eval 0 0
  have hg : g ∈ classNH (2 ^ r) H := ⟨T, ⟨hWF, (uniformTree_numLeaves _ r 0 0).le, hheight⟩, rfl⟩
  refine ⟨g, hg, ?_, (nodal_error_le hr hV hu).trans ?_⟩
  · apply LipschitzOnWith.continuousOn (K := (H : NNReal))
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx z hz
    simp only [Real.dist_eq, NNReal.coe_natCast]
    exact classNH_lipschitz hg hx hz
  · apply ENNReal.ofReal_le_ofReal
    calc (∑ j ∈ Finset.range (2 ^ r + 1), |y j - (V (j : ℤ) : ℝ)|) / (2 : ℝ) ^ r
        ≤ (∑ j ∈ Finset.range (2 ^ r + 1), (32 * w j / (H : ℝ))) / (2 : ℝ) ^ r := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply Finset.sum_le_sum
          intro j hj
          have hj' : j ≤ (2 : ℕ) ^ r := by simpa using Finset.mem_range.mp hj
          refine (hVerr j).trans ?_
          rw [div_le_div_iff₀ (by positivity) hHpos]
          linarith [(he j hj').2]
      _ = _ := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
        field_simp
        rfl

end FormalizacaoAltura
