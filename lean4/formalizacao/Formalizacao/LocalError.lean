import Formalizacao.QuasiGrid

/-!
# Lema 5.2(b) do artigo: erro local do quase-interpolante em `L^p`

Para `f` mensurável, integrável em `[0,1]`, com `f ∈ L^p([0,1])`, e para qualquer função
afim `a(y) = α + βy`, vale, para `k < n`,

  `‖f - Q_n f‖_{L^p(I_k)} ≤ 9 ‖f - a‖_{L^p(J_k)}`,

com `J_k = [t_m, t_{m+2}]`, `m = min(k, n-2)`, a união das duas células de `Q_n` usadas em `I_k`.
Tomar o ínfimo em `a` dá `9 E(f, J_k)_p`.

Prova: (i) `Q_n` é linear em `f` e reproduz `a`, logo `f - Q_n f = g - Q_n g` em `I_k`,
com `g = f - a`; (ii) em `I_k` só `φ_k` e `φ_{k+1}` são não nulos; (iii) a cota nodal
`|λ_j(g)| ≤ 4 n^{1/p} ‖g‖_{L^p(I_{c(j)})}` (`abs_lam_le`); (iv) `‖φ_j‖_{L^p(I_k)} ≤ n^{-1/p}`;
(v) Minkowski.
-/

open scoped ENNReal
open MeasureTheory Set

namespace FormalizacaoGrid

open FormalizacaoQuasi

/-- Norma `L^p` de `h` restrita a `S`, com expoente real `p`. -/
noncomputable def Np (p : ℝ) (h : ℝ → ℝ) (S : Set ℝ) : ℝ≥0∞ :=
  eLpNorm h (ENNReal.ofReal p) (volume.restrict S)

/-- Medida de `I_k`. -/
lemma volume_cell {n k : ℕ} (hn : 1 ≤ n) : volume (cell n k) = ENNReal.ofReal (1 / n) := by
  unfold cell
  rw [Real.volume_Icc]
  congr 1
  have := tn_succ n k hn
  linarith

/-- `0 ≤ φ_j ≤ 1`. -/
lemma hat_bounds (n j : ℕ) (x : ℝ) : 0 ≤ hat n j x ∧ hat n j x ≤ 1 := by
  unfold hat
  refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
  have : 0 ≤ |x - tn n j| * n := by positivity
  linarith

/-- `‖φ_j‖_{L^p(I_k)} ≤ n^{-1/p}`. -/
theorem Np_hat_le {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 1 ≤ p) (j k : ℕ) :
    Np p (hat n j) (cell n k) ≤ ENNReal.ofReal ((1 / (n : ℝ)) ^ (1 / p)) := by
  unfold Np
  have hb : ∀ᵐ x ∂(volume.restrict (cell n k)), ‖hat n j x‖ ≤ 1 := by
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hat_bounds n j x).1]
    exact (hat_bounds n j x).2
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by linarith)
  have hp0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  refine (eLpNorm_le_of_ae_bound hb).trans ?_
  rw [Measure.restrict_apply_univ, volume_cell hn, hpr, ENNReal.ofReal_one, mul_one,
    ENNReal.ofReal_rpow_of_nonneg hp0 (by positivity), one_div p]

/-- Subconjunto: `I_i ⊆ J_m` quando `m ≤ i` e `i+1 ≤ m+2`. -/
lemma cell_sub_J {n m i : ℕ} (h1 : m ≤ i) (h2 : i + 1 ≤ m + 2) :
    cell n i ⊆ Icc (tn n m) (tn n (m + 2)) := by
  intro x hx
  exact ⟨le_trans (tn_mono n h1) hx.1, le_trans hx.2 (tn_mono n h2)⟩

/-- Linearidade do núcleo: `∫_I k (f - aff) = ∫_I k f - ∫_I k aff`, com `k` limitado em `I`. -/
theorem integral_kern_sub {a b C α β : ℝ} {kern : ℝ → ℝ} (hkm : Measurable kern)
    (hkb : ∀ y ∈ Icc a b, |kern y| ≤ C) {f : ℝ → ℝ} (hfi : IntegrableOn f (Icc a b)) :
    ∫ y in Icc a b, kern y * (f y - (α + β * y)) =
      (∫ y in Icc a b, kern y * f y) - ∫ y in Icc a b, kern y * (α + β * y) := by
  have hI1 : IntegrableOn (fun y => kern y * f y) (Icc a b) := by
    refine Integrable.bdd_mul (c := C) hfi hkm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    rw [Real.norm_eq_abs]
    exact hkb y hy
  have hI2 : IntegrableOn (fun y => kern y * (α + β * y)) (Icc a b) := by
    have hc : Continuous fun y : ℝ => α + β * y := by fun_prop
    refine Integrable.bdd_mul (c := C) (hc.integrableOn_Icc) hkm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    rw [Real.norm_eq_abs]
    exact hkb y hy
  have hfun : (fun y => kern y * (f y - (α + β * y))) =
      fun y => kern y * f y - kern y * (α + β * y) := by
    funext y; ring
  rw [hfun]
  exact integral_sub hI1 hI2

/-- `λ_j` é linear: `λ_j(f - a) = λ_j(f) - λ_j(a)`. -/
theorem lam_sub {n : ℕ} (hn : 1 ≤ n) {f : ℝ → ℝ} (α β : ℝ) (j : ℕ) (hj : j ≤ n)
    (hfi : ∀ i, i < n → IntegrableOn f (cell n i)) :
    lam n (fun y => f y - (α + β * y)) j = lam n f j - lam n (fun y => α + β * y) j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓ : (0 : ℝ) < 1 / n := by positivity
  unfold lam
  split_ifs with hjn
  · -- célula `j`, extremo esquerdo
    have hcell := tn_succ n j hn
    have hfi' : IntegrableOn f (Icc (tn n j) (tn n (j + 1))) := hfi j hjn
    have hbound : ∀ y ∈ Icc (tn n j) (tn n (j + 1)), |kL (tn n j) (1 / n) y| ≤ 4 / (1 / n) := by
      intro y hy
      have hy' : y ∈ Icc (tn n j) (tn n j + 1 / n) := by rw [← hcell]; exact hy
      exact abs_kL_le hℓ hy'
    exact integral_kern_sub (C := 4 / (1 / n)) (kern := kL (tn n j) (1 / n))
      (by unfold kL; fun_prop) hbound hfi'
  · -- célula `n - 1`, extremo direito
    have hcell := tn_succ n (n - 1) hn
    have hfi' : IntegrableOn f (Icc (tn n (n - 1)) (tn n (n - 1 + 1))) := hfi (n - 1) (by omega)
    have hbound : ∀ y ∈ Icc (tn n (n - 1)) (tn n (n - 1 + 1)),
        |kR (tn n (n - 1)) (1 / n) y| ≤ 4 / (1 / n) := by
      intro y hy
      have hy' : y ∈ Icc (tn n (n - 1)) (tn n (n - 1) + 1 / n) := by rw [← hcell]; exact hy
      exact abs_kR_le hℓ hy'
    exact integral_kern_sub (C := 4 / (1 / n)) (kern := kR (tn n (n - 1)) (1 / n))
      (by unfold kR; fun_prop) hbound hfi'

/-- Índice da célula de `λ_j` com `j ∈ {k, k+1}` cai em `{m, m+1}`, `m = min(k, n-2)`. -/
lemma cellIdx_mem {n k j : ℕ} (hn : 2 ≤ n) (hk : k < n) (hj : j = k ∨ j = k + 1) :
    min k (n - 2) ≤ cellIdx n j ∧ cellIdx n j + 1 ≤ min k (n - 2) + 2 := by
  unfold cellIdx
  omega

/-- Células `I_i`, com `i < n`, estão em `[0,1]`. -/
lemma cell_sub_unit {n i : ℕ} (hi : i < n) : cell n i ⊆ Icc 0 1 := by
  intro x hx
  have h0 : tn n 0 = 0 := by simp [tn]
  have h1 : tn n n = 1 := by
    unfold tn
    have : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      exact_mod_cast this.ne'
    field_simp
  have hA : 0 ≤ tn n i := by unfold tn; positivity
  have hB : tn n (i + 1) ≤ 1 := by
    rw [← h1]; exact tn_mono n (by omega)
  exact ⟨le_trans hA hx.1, le_trans hx.2 hB⟩

/-- Cota da parcela nodal: `‖λ_j(g) φ_j‖_{L^p(I_k)} ≤ 4 ‖g‖_{L^p(I_{c(j)})}`. -/
theorem Np_lam_hat {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 1 ≤ p) {g : ℝ → ℝ} (hgm : Measurable g)
    (j : ℕ) (hj : j ≤ n) (k : ℕ)
    (hfin : Np p g (cell n (cellIdx n j)) < ⊤) :
    Np p (fun x => lam n g j * hat n j x) (cell n k) ≤
      ENNReal.ofReal 4 * Np p g (cell n (cellIdx n j)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hid : (n : ℝ) ^ (1 / p) * (1 / (n : ℝ)) ^ (1 / p) = 1 := by
    rw [← Real.mul_rpow hn0.le (by positivity), mul_one_div_cancel hn0.ne', Real.one_rpow]
  set c := lam n g j with hc
  set e := (Np p g (cell n (cellIdx n j))).toReal with he
  have hlam : |c| ≤ 4 * (n : ℝ) ^ (1 / p) * e := abs_lam_le hn hp j hj hgm hfin
  have hsmul : (fun x => c * hat n j x) = c • hat n j := by funext x; simp [smul_eq_mul]
  unfold Np at *
  rw [hsmul, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
  have hpow0 : (0 : ℝ) ≤ (n : ℝ) ^ (1 / p) := by positivity
  have hbound := Np_hat_le hn hp j k
  unfold Np at hbound
  calc ENNReal.ofReal |c| * eLpNorm (hat n j) (ENNReal.ofReal p) (volume.restrict (cell n k))
      ≤ ENNReal.ofReal (4 * (n : ℝ) ^ (1 / p) * e) *
          ENNReal.ofReal ((1 / (n : ℝ)) ^ (1 / p)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hlam) hbound
    _ = ENNReal.ofReal (4 * e) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc 4 * (n : ℝ) ^ (1 / p) * e * (1 / (n : ℝ)) ^ (1 / p)
            = 4 * e * ((n : ℝ) ^ (1 / p) * (1 / (n : ℝ)) ^ (1 / p)) := by ring
          _ = 4 * e := by rw [hid, mul_one]
    _ = ENNReal.ofReal 4 * Np p g (cell n (cellIdx n j)) := by
        rw [ENNReal.ofReal_mul (by norm_num), he, ENNReal.ofReal_toReal hfin.ne] <;> rfl

/-- Chapéus são mensuráveis. -/
lemma hat_measurable (n j : ℕ) : Measurable (hat n j) := by
  apply Continuous.measurable
  unfold hat
  fun_prop

/-- **Lema 5.2(b).** Para `f` mensurável, integrável e em `L^p([0,1])`, `k < n` e uma função
afim `a`, `‖f - Q_n f‖_{L^p(I_k)} ≤ 9 ‖f - a‖_{L^p(J_k)}`, com `J_k = [t_m, t_{m+2}]`,
`m = min(k, n-2)`. -/
theorem local_error {p : ℝ} (hp : 1 ≤ p) {n : ℕ} (hn : 2 ≤ n) {k : ℕ} (hk : k < n)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi0 : IntegrableOn f (Icc 0 1))
    (hfin0 : Np p f (Icc 0 1) < ⊤) (α β : ℝ) :
    Np p (fun x => f x - Q n f x) (cell n k) ≤
      9 * Np p (fun x => f x - (α + β * x))
        (Icc (tn n (min k (n - 2))) (tn n (min k (n - 2) + 2))) := by
  have hn1 : 1 ≤ n := by omega
  set J := Icc (tn n (min k (n - 2))) (tn n (min k (n - 2) + 2)) with hJ
  set g : ℝ → ℝ := fun x => f x - (α + β * x) with hg
  have hgm : Measurable g := hf.sub (by fun_prop)
  by_cases hJtop : Np p g J = ⊤
  · rw [hJtop, ENNReal.mul_top (by norm_num)]
    exact le_top
  have hJfin : Np p g J < ⊤ := lt_top_iff_ne_top.2 hJtop
  have hmono : ∀ S : Set ℝ, S ⊆ J → Np p g S ≤ Np p g J := by
    intro S hS
    unfold Np
    exact eLpNorm_mono_measure g (Measure.restrict_mono hS le_rfl)
  have hfi : ∀ i, i < n → IntegrableOn f (cell n i) := fun i hi =>
    hfi0.mono_set (cell_sub_unit hi)
  -- linearidade de Q_n em f
  have hQlin : ∀ x, Q n f x = Q n g x + Q n (fun y => α + β * y) x := by
    intro x
    unfold Q
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by
      rw [Finset.mem_range] at hj
      omega
    rw [hg, lam_sub hn1 α β j hjn hfi]
    ring
  -- identidade em I_k
  have hpt : ∀ x ∈ cell n k, f x - Q n f x = g x - Q n g x := by
    intro x hx
    rw [hQlin x, Q_affine hn1 hk α β hx, hg]
    ring
  have hcellm : MeasurableSet (cell n k) := measurableSet_Icc
  have hae : (fun x => f x - Q n f x) =ᵐ[volume.restrict (cell n k)]
      (fun x => g x - Q n g x) :=
    Filter.eventually_of_mem (ae_restrict_mem hcellm) hpt
  unfold Np at hmono hJfin ⊢
  rw [eLpNorm_congr_ae hae]
  -- em I_k, Q_n g tem dois termos
  have hae2 : (fun x => g x - Q n g x) =ᵐ[volume.restrict (cell n k)]
      (fun x => g x - (lam n g k * hat n k x + lam n g (k + 1) * hat n (k + 1) x)) :=
    Filter.eventually_of_mem (ae_restrict_mem hcellm) (fun x hx => by
      show g x - Q n g x = _
      rw [Q_cell hn1 hk g hx])
  rw [eLpNorm_congr_ae hae2]
  set A : ℝ → ℝ := fun x => lam n g k * hat n k x with hA
  set B : ℝ → ℝ := fun x => lam n g (k + 1) * hat n (k + 1) x with hB
  have hAm : Measurable A := measurable_const.mul (hat_measurable n k)
  have hBm : Measurable B := measurable_const.mul (hat_measurable n (k + 1))
  have hsplit : (fun x => g x - (lam n g k * hat n k x + lam n g (k + 1) * hat n (k + 1) x)) =
      (fun x => (g x + -A x) + -B x) := by
    funext x
    simp only [hA, hB]
    ring
  rw [hsplit]
  -- índices das células de λ_k e λ_{k+1}
  have hsub0 : cell n (cellIdx n k) ⊆ J := by
    obtain ⟨h1, h2⟩ := cellIdx_mem hn (show k < n from hk) (Or.inl rfl)
    exact cell_sub_J h1 h2
  have hsub1 : cell n (cellIdx n (k + 1)) ⊆ J := by
    obtain ⟨h1, h2⟩ := cellIdx_mem hn (show k < n from hk) (Or.inr rfl)
    exact cell_sub_J h1 h2
  have hfin0' : Np p g (cell n (cellIdx n k)) < ⊤ := lt_of_le_of_lt (hmono _ hsub0) hJfin
  have hfin1' : Np p g (cell n (cellIdx n (k + 1))) < ⊤ := lt_of_le_of_lt (hmono _ hsub1) hJfin
  have hkn : k ≤ n := le_of_lt hk
  have hk1 : k + 1 ≤ n := hk
  have hA' := Np_lam_hat hn1 hp hgm k hkn k hfin0'
  have hB' := Np_lam_hat hn1 hp hgm (k + 1) hk1 k hfin1'
  -- Minkowski
  have h1p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hm1 : eLpNorm (fun x => (g x + -A x) + -B x) (ENNReal.ofReal p)
      (volume.restrict (cell n k)) ≤
      eLpNorm (fun x => g x + -A x) (ENNReal.ofReal p) (volume.restrict (cell n k)) +
        eLpNorm (fun x => -B x) (ENNReal.ofReal p) (volume.restrict (cell n k)) :=
    eLpNorm_add_le (hgm.add hAm.neg).aestronglyMeasurable hBm.neg.aestronglyMeasurable h1p
  have hm2 : eLpNorm (fun x => g x + -A x) (ENNReal.ofReal p) (volume.restrict (cell n k)) ≤
      eLpNorm g (ENNReal.ofReal p) (volume.restrict (cell n k)) +
        eLpNorm (fun x => -A x) (ENNReal.ofReal p) (volume.restrict (cell n k)) :=
    eLpNorm_add_le hgm.aestronglyMeasurable hAm.neg.aestronglyMeasurable h1p
  have hnegA : eLpNorm (fun x => -A x) (ENNReal.ofReal p) (volume.restrict (cell n k)) =
      eLpNorm A (ENNReal.ofReal p) (volume.restrict (cell n k)) := eLpNorm_neg A _ _
  have hnegB : eLpNorm (fun x => -B x) (ENNReal.ofReal p) (volume.restrict (cell n k)) =
      eLpNorm B (ENNReal.ofReal p) (volume.restrict (cell n k)) := eLpNorm_neg B _ _
  have hcellk : eLpNorm g (ENNReal.ofReal p) (volume.restrict (cell n k)) ≤
      eLpNorm g (ENNReal.ofReal p) (volume.restrict J) :=
    eLpNorm_mono_measure g (Measure.restrict_mono (cell_sub_J (show min k (n - 2) ≤ k by omega)
      (show k + 1 ≤ min k (n - 2) + 2 by omega)) le_rfl)
  have hA'' : eLpNorm A (ENNReal.ofReal p) (volume.restrict (cell n k)) ≤
      ENNReal.ofReal 4 * eLpNorm g (ENNReal.ofReal p) (volume.restrict J) := by
    have h := hA'
    unfold Np at h
    exact h.trans (mul_le_mul_left' (hmono _ hsub0) _)
  have hB'' : eLpNorm B (ENNReal.ofReal p) (volume.restrict (cell n k)) ≤
      ENNReal.ofReal 4 * eLpNorm g (ENNReal.ofReal p) (volume.restrict J) := by
    have h := hB'
    unfold Np at h
    exact h.trans (mul_le_mul_left' (hmono _ hsub1) _)
  have h4 : ENNReal.ofReal 4 = 4 := by norm_num
  calc eLpNorm (fun x => (g x + -A x) + -B x) (ENNReal.ofReal p) (volume.restrict (cell n k))
      ≤ eLpNorm (fun x => g x + -A x) (ENNReal.ofReal p) (volume.restrict (cell n k)) +
          eLpNorm (fun x => -B x) (ENNReal.ofReal p) (volume.restrict (cell n k)) := hm1
    _ ≤ (eLpNorm g (ENNReal.ofReal p) (volume.restrict (cell n k)) +
          eLpNorm (fun x => -A x) (ENNReal.ofReal p) (volume.restrict (cell n k))) +
          eLpNorm (fun x => -B x) (ENNReal.ofReal p) (volume.restrict (cell n k)) :=
        add_le_add hm2 le_rfl
    _ = eLpNorm g (ENNReal.ofReal p) (volume.restrict (cell n k)) +
          eLpNorm A (ENNReal.ofReal p) (volume.restrict (cell n k)) +
          eLpNorm B (ENNReal.ofReal p) (volume.restrict (cell n k)) := by
        rw [hnegA, hnegB]
    _ ≤ eLpNorm g (ENNReal.ofReal p) (volume.restrict J) +
          ENNReal.ofReal 4 * eLpNorm g (ENNReal.ofReal p) (volume.restrict J) +
          ENNReal.ofReal 4 * eLpNorm g (ENNReal.ofReal p) (volume.restrict J) :=
        add_le_add (add_le_add hcellk hA'') hB''
    _ = 9 * eLpNorm g (ENNReal.ofReal p) (volume.restrict J) := by
        rw [h4]
        ring

end FormalizacaoGrid
