import Formalizacao.MinimaxDefs
import Formalizacao.AlturaFloor
import Formalizacao.LpAxioms

/-!
# F2.2 — Empacotamento de bumps (`lp:lem:packing`)

Função-teste: `φB` (de `AlturaFloor`), suave, com suporte em `(1/8, 5/8) ⊂ (0,1)`.
Para `m ∈ ℕ`, `A ∈ ℝ` e `x ∈ ℝ`, a soma de bumps é `A · Σ_{j<m} φB(m x - j)`.

Esta primeira parte demonstra os fatos combinatórios e pontuais:

* `φB`-suporte e `D2 u φ`, a segunda diferença com passo `u`;
* a identidade `diff2 h (φ(m·-j)) = D2 (m h) φ (m· - j)`;
* **overlap ≤ 3**: para cada `x`, no máximo três `j < m` têm `D2 u φB (m x - j) ≠ 0`;
* a desigualdade de potência `|Σ_{j} a_j|^p ≤ 3^{p-1} Σ_{j} |a_j|^p`, para `a_j = D2 u φB (m x - j)`.
-/

open scoped ENNReal
open MeasureTheory Set Finset

namespace FormalizacaoPacking

open FormalizacaoAltura FormalizacaoLp

/-- Segunda diferença com passo `u` de uma função `φ` em `y`: `φ(y+2u) - 2φ(y+u) + φ(y)`. -/
noncomputable def D2 (u : ℝ) (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  φ (y + 2 * u) - 2 * φ (y + u) + φ y

/-- Se `φB z ≠ 0`, então `z ∈ (1/8, 5/8)`. -/
lemma mem_of_φB_ne_zero {z : ℝ} (h : φB z ≠ 0) : z ∈ Ioo (1 / 8 : ℝ) (5 / 8) := by
  by_contra hz
  exact h (φB_eq_zero_of_not_mem hz)

/-- Identidade de escala: a segunda diferença de `x ↦ φB(m x - j)` com passo `h` é
`D2 (m h) φB` avaliada em `m x - j`. -/
lemma diff2_scaled (m : ℕ) (h : ℝ) (j : ℕ) (x : ℝ) :
    FormalizacaoLp.diff2 h (fun y : ℝ => φB (m * y - j)) x
      = D2 (m * h) φB (m * x - j) := by
  unfold FormalizacaoLp.diff2 D2
  have e1 : (m : ℝ) * (x + 2 * h) - j = (m * x - j) + 2 * (m * h) := by ring
  have e2 : (m : ℝ) * (x + h) - j = (m * x - j) + (m * h) := by ring
  simp only [e1, e2]

/-- Overlap: para cada `x` e `u`, existe um conjunto de no máximo três índices `j` fora do
qual `D2 u φB (m x - j) = 0`. -/
lemma overlap_le_three (m : ℕ) (u x : ℝ) :
    ((range m).filter (fun j : ℕ => D2 u φB (m * x - j) ≠ 0)).card ≤ 3 := by
  set S : Finset ℤ := (Finset.univ : Finset (Fin 3)).image
    (fun k : Fin 3 => ⌊(m : ℝ) * x + (k : ℝ) * u - 1 / 8⌋) with hS
  have hcardS : S.card ≤ 3 := by
    rw [hS]
    exact (Finset.card_image_le).trans (by simp)
  refine le_trans ?_ hcardS
  refine Finset.card_le_card_of_injOn (fun j : ℕ => (j : ℤ)) ?_ ?_
  · intro j hj
    rw [Finset.mem_coe, Finset.mem_filter] at hj
    have hne := hj.2
    unfold D2 at hne
    -- uma das três avaliações de `φB` é não nula
    have hk : ∃ k : Fin 3, φB (m * x - j + (k : ℝ) * u) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hne
      have h0 := hcon 0
      have h1 := hcon 1
      have h2 := hcon 2
      simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero, Fin.val_one, Nat.cast_one,
        one_mul, Fin.val_two, Nat.cast_ofNat] at h0 h1 h2
      have e1 : (m : ℝ) * x - j + 2 * u = (m * x - j + (2 : ℝ) * u) := by ring
      rw [h0, h1, h2]; ring
    obtain ⟨k, hk⟩ := hk
    have hmem := mem_of_φB_ne_zero hk
    obtain ⟨hlo, hhi⟩ := hmem
    have hfl : ⌊(m : ℝ) * x + (k : ℝ) * u - 1 / 8⌋ = (j : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast; linarith
      · push_cast; linarith
    rw [Finset.mem_coe, hS, Finset.mem_image]
    exact ⟨k, Finset.mem_univ _, hfl⟩
  · intro a _ b _ hab
    exact Nat.cast_injective hab

/-! ## Mudança de variável afim e desigualdade de potência -/

/-- `∫⁻ g(a x - j) dx = a⁻¹ ∫⁻ g`, para `a > 0`. -/
lemma lint_affine (a : ℝ) (ha : 0 < a) (j : ℝ) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x, g (a * x - j) = ENNReal.ofReal a⁻¹ * ∫⁻ y, g y := by
  have hf : Measurable (fun x : ℝ => a * x - j) := (measurable_const_mul a).sub_const j
  have hmap : Measure.map (fun x : ℝ => a * x - j) volume = ENNReal.ofReal a⁻¹ • volume := by
    have h1 : (fun x : ℝ => a * x - j) = (fun z : ℝ => z - j) ∘ (fun x : ℝ => a * x) := rfl
    rw [h1, ← Measure.map_map (measurable_sub_const j) (measurable_const_mul a),
      Real.map_volume_mul_left ha.ne', Measure.map_smul]
    rw [abs_of_pos (inv_pos.mpr ha)]
    congr 1
    have := MeasureTheory.Measure.IsAddRightInvariant.map_add_right_eq_self
      (μ := (volume : Measure ℝ)) (-j)
    simpa [sub_eq_add_neg] using this
  rw [← lintegral_map hg hf, hmap, lintegral_smul_measure, smul_eq_mul]

/-- `|Σ_j c_j|^p ≤ 3^{p-1} Σ_j |c_j|^p` se no máximo três `c_j` são não nulos. -/
lemma sum_rpow_le_three {p : ℝ} (hp : 1 ≤ p) (c : ℕ → ℝ) (m : ℕ)
    (hT : ((range m).filter (fun j => c j ≠ 0)).card ≤ 3) :
    |∑ j ∈ range m, c j| ^ p ≤ (3 : ℝ) ^ (p - 1) * ∑ j ∈ range m, |c j| ^ p := by
  set T := (range m).filter (fun j => c j ≠ 0) with hTdef
  have h1 : ∑ j ∈ T, c j = ∑ j ∈ range m, c j :=
    Finset.sum_filter_of_ne (fun j _ hj => hj)
  have hp0 : 0 ≤ p := by linarith
  have h2 : |∑ j ∈ range m, c j| ≤ ∑ j ∈ T, |c j| := by
    rw [← h1]; exact Finset.abs_sum_le_sum_abs _ _
  have h3 : (∑ j ∈ T, |c j|) ^ p ≤ (T.card : ℝ) ^ (p - 1) * ∑ j ∈ T, |c j| ^ p :=
    Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := T) (f := fun j => |c j|) hp (fun j _ => abs_nonneg _)
  have h4 : (T.card : ℝ) ^ (p - 1) ≤ (3 : ℝ) ^ (p - 1) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hT) (by linarith)
  have h5 : ∑ j ∈ T, |c j| ^ p ≤ ∑ j ∈ range m, |c j| ^ p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j _ _ => by positivity)
  have h6 : |∑ j ∈ range m, c j| ^ p ≤ (∑ j ∈ T, |c j|) ^ p :=
    Real.rpow_le_rpow (abs_nonneg _) h2 hp0
  have hsT : 0 ≤ ∑ j ∈ T, |c j| ^ p := Finset.sum_nonneg (fun j _ => by positivity)
  calc |∑ j ∈ range m, c j| ^ p ≤ (∑ j ∈ T, |c j|) ^ p := h6
    _ ≤ (T.card : ℝ) ^ (p - 1) * ∑ j ∈ T, |c j| ^ p := h3
    _ ≤ (3 : ℝ) ^ (p - 1) * ∑ j ∈ T, |c j| ^ p := mul_le_mul_of_nonneg_right h4 hsT
    _ ≤ (3 : ℝ) ^ (p - 1) * ∑ j ∈ range m, |c j| ^ p :=
        mul_le_mul_of_nonneg_left h5 (by positivity)

/-- A soma de bumps com amplitude `A`. -/
noncomputable def Fm (m : ℕ) (A : ℝ) (x : ℝ) : ℝ :=
  A * ∑ j ∈ range m, φB (m * x - j)

/-- Segunda diferença de `Fm`. -/
lemma diff2_Fm (m : ℕ) (A h x : ℝ) :
    FormalizacaoLp.diff2 h (Fm m A) x = A * ∑ j ∈ range m, D2 (m * h) φB (m * x - j) := by
  unfold FormalizacaoLp.diff2 Fm D2
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have e1 : (m : ℝ) * (x + 2 * h) - j = (m * x - j) + 2 * (m * h) := by ring
  have e2 : (m : ℝ) * (x + h) - j = (m * x - j) + (m * h) := by ring
  rw [e1, e2]; ring

/-- Cota pontual com overlap ≤ 3. -/
lemma diff2_Fm_pow_le {p : ℝ} (hp : 1 ≤ p) (m : ℕ) (A h x : ℝ) :
    |FormalizacaoLp.diff2 h (Fm m A) x| ^ p ≤
      (3 : ℝ) ^ (p - 1) * |A| ^ p * ∑ j ∈ range m, |D2 (m * h) φB (m * x - j)| ^ p := by
  rw [diff2_Fm]
  have hT : ((range m).filter (fun j : ℕ => A * D2 (m * h) φB (m * x - j) ≠ 0)).card ≤ 3 := by
    refine le_trans (Finset.card_le_card ?_) (overlap_le_three m (m * h) x)
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, fun h0 => hj.2 (by rw [h0, mul_zero])⟩
  have key := sum_rpow_le_three hp (fun j : ℕ => A * D2 (m * h) φB (m * x - j)) m hT
  rw [← Finset.mul_sum, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)] at key
  have e : ∑ j ∈ range m, |A * D2 (m * h) φB (m * x - j)| ^ p
      = |A| ^ p * ∑ j ∈ range m, |D2 (m * h) φB (m * x - j)| ^ p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  simp only [e] at key
  nlinarith [key]


/-! ## Integral da `p`-ésima potência da segunda diferença -/

lemma continuous_D2 (u : ℝ) : Continuous (D2 u φB) := by
  have hc : Continuous φB := φB_smooth.continuous
  unfold D2
  fun_prop

/-- `Ipow p u = ∫ |D2 u φB|^p`. -/
noncomputable def Ipow (p u : ℝ) : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (|D2 u φB y| ^ p)

lemma measurable_Ipow_integrand {p : ℝ} (hp : 0 ≤ p) (u : ℝ) :
    Measurable (fun y => ENNReal.ofReal (|D2 u φB y| ^ p)) := by
  have : Continuous (fun y => |D2 u φB y| ^ p) :=
    ((continuous_D2 u).abs).rpow_const (fun _ => Or.inr hp)
  exact ENNReal.measurable_ofReal.comp this.measurable

/-- Estimativa integral da segunda diferença da soma de bumps. -/
lemma lint_diff_le {p : ℝ} (hp : 1 ≤ p) {m : ℕ} (hm : 1 ≤ m) (A h : ℝ) :
    ∫⁻ x, ENNReal.ofReal (|FormalizacaoLp.diff2 h (Fm m A) x| ^ p)
      ≤ ENNReal.ofReal ((3 : ℝ) ^ (p - 1) * |A| ^ p) * Ipow p (m * h) := by
  have hp0 : 0 ≤ p := by linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set c : ℝ := (3 : ℝ) ^ (p - 1) * |A| ^ p with hc
  have hc0 : 0 ≤ c := by positivity
  calc ∫⁻ x, ENNReal.ofReal (|FormalizacaoLp.diff2 h (Fm m A) x| ^ p)
      ≤ ∫⁻ x, ENNReal.ofReal c *
          ∑ j ∈ range m, ENNReal.ofReal (|D2 (m * h) φB (m * x - j)| ^ p) := by
        refine lintegral_mono (fun x => ?_)
        have h1 := diff2_Fm_pow_le hp m A h x
        calc ENNReal.ofReal (|FormalizacaoLp.diff2 h (Fm m A) x| ^ p)
            ≤ ENNReal.ofReal (c * ∑ j ∈ range m, |D2 (m * h) φB (m * x - j)| ^ p) := by
              apply ENNReal.ofReal_le_ofReal
              calc _ ≤ _ := h1
                _ = _ := by rw [hc]; try ring
          _ = _ := by
              rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_sum_of_nonneg
                (fun j _ => by positivity)]
    _ = ENNReal.ofReal c * ∑ j ∈ range m,
          ∫⁻ x, ENNReal.ofReal (|D2 (m * h) φB (m * x - j)| ^ p) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [lintegral_finset_sum]
        intro j _
        have := (measurable_Ipow_integrand hp0 (m * h))
        exact this.comp ((measurable_const_mul (m : ℝ)).sub_const (j : ℝ))
    _ = ENNReal.ofReal c * ∑ j ∈ range m, (ENNReal.ofReal (m : ℝ)⁻¹ * Ipow p (m * h)) := by
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        exact lint_affine (m : ℝ) hmpos (j : ℝ)
          (fun y => ENNReal.ofReal (|D2 (m * h) φB y| ^ p)) (measurable_Ipow_integrand hp0 _)
    _ = ENNReal.ofReal c * Ipow p (m * h) := by
        have hm1 : (m : ℝ≥0∞) * ENNReal.ofReal (m : ℝ)⁻¹ = 1 := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            mul_inv_cancel₀ hmpos.ne', ENNReal.ofReal_one]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc (m : ℝ≥0∞), hm1, one_mul]

/-! ## Estimativas `L^p` -/

lemma eLpNorm_le_of_lint {p : ℝ} (hp : 1 ≤ p) {μ : Measure ℝ} {f : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (h : ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ ≤ ENNReal.ofReal (K ^ p)) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K := by
  have hp0 : 0 < p := by linarith
  have hne0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  have e : ∀ x, ‖f x‖ₑ ^ p = ENNReal.ofReal (|f x| ^ p) := fun x => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
  simp only [e]
  calc (∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ) ^ (1 / p)
      ≤ (ENNReal.ofReal (K ^ p)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal K := by
        rw [← ENNReal.ofReal_rpow_of_nonneg hK hp0.le, ← ENNReal.rpow_mul,
          mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-- `Σ_j φB(m x - j)` tem no máximo um termo não nulo. -/
lemma abs_sum_bump_le (m : ℕ) (x : ℝ) : |∑ j ∈ range m, φB (m * x - j)| ≤ 1 := by
  set T := (range m).filter (fun j : ℕ => φB (m * x - j) ≠ 0) with hT
  have hcard : T.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [hT, Finset.mem_filter] at ha hb
    obtain ⟨lo1, hi1⟩ := mem_of_φB_ne_zero ha.2
    obtain ⟨lo2, hi2⟩ := mem_of_φB_ne_zero hb.2
    have h1 : (a : ℝ) < b + 1 := by linarith
    have h2 : (b : ℝ) < a + 1 := by linarith
    have h1' : a < b + 1 := by exact_mod_cast h1
    have h2' : b < a + 1 := by exact_mod_cast h2
    omega
  have hsum : ∑ j ∈ T, φB (m * x - j) = ∑ j ∈ range m, φB (m * x - j) :=
    Finset.sum_filter_of_ne (fun j _ hj => hj)
  rw [← hsum]
  calc |∑ j ∈ T, φB (m * x - j)| ≤ ∑ j ∈ T, |φB (m * x - j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ T, (1 : ℝ) := Finset.sum_le_sum (fun j _ => φB_abs_le _)
    _ = T.card := by simp
    _ ≤ 1 := by exact_mod_cast hcard

lemma abs_Fm_le (m : ℕ) (A x : ℝ) : |Fm m A x| ≤ |A| := by
  unfold Fm
  rw [abs_mul]
  calc |A| * |∑ j ∈ range m, φB (m * x - j)| ≤ |A| * 1 :=
        mul_le_mul_of_nonneg_left (abs_sum_bump_le m x) (abs_nonneg _)
    _ = |A| := mul_one _

lemma eLpNorm_Fm_le {p : ℝ} (hp : 1 ≤ p) (m : ℕ) (A : ℝ) :
    eLpNorm (Fm m A) (ENNReal.ofReal p) vol01 ≤ ENNReal.ofReal |A| := by
  have hp0 : 0 < p := by linarith
  have hb : ∀ᵐ x ∂vol01, ‖Fm m A x‖ ≤ |A| :=
    Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact abs_Fm_le m A x)
  have := eLpNorm_le_of_ae_bound (p := ENNReal.ofReal p) hb
  have hv : vol01 Set.univ = 1 := by simp [vol01, Real.volume_Icc]
  rw [hv, ENNReal.one_rpow, one_mul] at this
  exact this

/-- `D2 u φB` anula-se fora de `[-2,1]` se `0 ≤ u ≤ 1`. -/
lemma D2_eq_zero_of_not_mem {u y : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hy : y ∉ Icc (-2 : ℝ) 1) : D2 u φB y = 0 := by
  unfold D2
  have hy' : y < -2 ∨ 1 < y := by
    by_contra hcon; push_neg at hcon; exact hy ⟨hcon.1, hcon.2⟩
  rcases hy' with h | h
  · have a1 : φB (y + 2 * u) = 0 := φB_eq_zero_of_not_mem (fun hm => by
      have := hm.1; linarith)
    have a2 : φB (y + u) = 0 := φB_eq_zero_of_not_mem (fun hm => by
      have := hm.1; linarith)
    have a3 : φB y = 0 := φB_eq_zero_of_not_mem (fun hm => by
      have := hm.1; linarith)
    rw [a1, a2, a3]; ring
  · have a1 : φB (y + 2 * u) = 0 := φB_eq_zero_of_not_mem (fun hm => by
      have := hm.2; linarith)
    have a2 : φB (y + u) = 0 := φB_eq_zero_of_not_mem (fun hm => by
      have := hm.2; linarith)
    have a3 : φB y = 0 := φB_eq_zero_of_not_mem (fun hm => by
      have := hm.2; linarith)
    rw [a1, a2, a3]; ring

lemma Ipow_small_le {p : ℝ} (hp : 1 ≤ p) {M : ℝ} (hM : ∀ z, |deriv (deriv φB) z| ≤ M)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Ipow p u ≤ ENNReal.ofReal ((M * u ^ 2) ^ p) * ENNReal.ofReal 3 := by
  have hp0 : 0 ≤ p := by linarith
  unfold Ipow
  have hb : ∀ y, ENNReal.ofReal (|D2 u φB y| ^ p) ≤
      (Icc (-2 : ℝ) 1).indicator (fun _ => ENNReal.ofReal ((M * u ^ 2) ^ p)) y := by
    intro y
    by_cases hy : y ∈ Icc (-2 : ℝ) 1
    · rw [Set.indicator_of_mem hy]
      apply ENNReal.ofReal_le_ofReal
      have h1 : |D2 u φB y| ≤ M * u ^ 2 := by
        unfold D2
        exact diff2_unit_le φB_diff deriv_φB_diff hM u y
      exact Real.rpow_le_rpow (abs_nonneg _) h1 hp0
    · rw [Set.indicator_of_notMem hy, D2_eq_zero_of_not_mem hu0 hu1 hy]
      simp only [abs_zero]
      rw [Real.zero_rpow (by linarith)]
      simp
  calc ∫⁻ y, ENNReal.ofReal (|D2 u φB y| ^ p)
      ≤ ∫⁻ y, (Icc (-2 : ℝ) 1).indicator (fun _ => ENNReal.ofReal ((M * u ^ 2) ^ p)) y :=
        lintegral_mono hb
    _ = ENNReal.ofReal ((M * u ^ 2) ^ p) * volume (Icc (-2 : ℝ) 1) :=
        lintegral_indicator_const measurableSet_Icc _
    _ = ENNReal.ofReal ((M * u ^ 2) ^ p) * ENNReal.ofReal 3 := by
        rw [Real.volume_Icc]; norm_num


lemma measurable_Fm (m : ℕ) (A : ℝ) : Measurable (Fm m A) := by
  have hc : Continuous φB := φB_smooth.continuous
  unfold Fm
  have : Continuous (fun x : ℝ => A * ∑ j ∈ range m, φB (m * x - j)) := by fun_prop
  exact this.measurable

/-- Estimativa uniforme do módulo de segunda ordem da soma de bumps (constante `K0`
independente de `p`, `m`, `A` e `t`). -/
theorem exists_K0 : ∃ K0 : ℝ, 0 < K0 ∧ ∀ {p : ℝ}, 1 ≤ p → ∀ {m : ℕ}, 1 ≤ m →
    ∀ (A t : ℝ), 0 < t →
      wtP (ENNReal.ofReal p) t (Fm m A) ≤
        ENNReal.ofReal (K0 * |A| * min 1 ((m * t) ^ 2)) := by
  obtain ⟨M, hM0, hM⟩ := exists_M_φB
  refine ⟨max 12 (3 * M), by positivity, ?_⟩
  intro p hp m hm A t ht
  have hp0 : 0 < p := by linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hK0 : 0 < max 12 (3 * M) := by positivity
  by_cases hmt : 1 ≤ (m : ℝ) * t
  · have hmin : min 1 (((m : ℝ) * t) ^ 2) = 1 := by
      apply min_eq_left; nlinarith
    rw [hmin]
    calc wtP (ENNReal.ofReal p) t (Fm m A)
        ≤ 4 * eLpNorm (Fm m A) (ENNReal.ofReal p) vol01 :=
          wtP_le_four (ENNReal.one_le_ofReal.mpr hp) t (measurable_Fm m A)
      _ ≤ 4 * ENNReal.ofReal |A| := by gcongr; exact eLpNorm_Fm_le hp m A
      _ = ENNReal.ofReal (4 * |A|) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have : (12 : ℝ) ≤ max 12 (3 * M) := le_max_left _ _
          nlinarith [abs_nonneg A]
  · push_neg at hmt
    have hmin : min 1 (((m : ℝ) * t) ^ 2) = ((m : ℝ) * t) ^ 2 := by
      apply min_eq_right
      have : 0 ≤ (m : ℝ) * t := by positivity
      nlinarith
    rw [hmin]
    unfold wtP
    refine iSup₂_le (fun h hh => ?_)
    have hh0 : 0 < h := hh.1
    have hht : h ≤ t := le_trans hh.2 (min_le_left _ _)
    set u : ℝ := (m : ℝ) * h with hu
    have hu0 : 0 ≤ u := by positivity
    have hut : u ≤ (m : ℝ) * t := by rw [hu]; exact mul_le_mul_of_nonneg_left hht hmpos.le
    have hu1 : u ≤ 1 := by linarith
    refine le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self) ?_
    have hK : 0 ≤ 3 * |A| * (M * u ^ 2) := by positivity
    have hint : ∫⁻ x, ENNReal.ofReal (|FormalizacaoLp.diff2 h (Fm m A) x| ^ p)
        ≤ ENNReal.ofReal ((3 * |A| * (M * u ^ 2)) ^ p) := by
      calc _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (p - 1) * |A| ^ p) * Ipow p u :=
            lint_diff_le hp hm A h
        _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (p - 1) * |A| ^ p) *
              (ENNReal.ofReal ((M * u ^ 2) ^ p) * ENNReal.ofReal 3) := by
            gcongr; exact Ipow_small_le hp hM hu0 hu1
        _ = ENNReal.ofReal ((3 * |A| * (M * u ^ 2)) ^ p) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            have e1 : (3 * |A| * (M * u ^ 2)) ^ p = (3 : ℝ) ^ p * |A| ^ p * (M * u ^ 2) ^ p := by
              rw [Real.mul_rpow (by positivity) (by positivity),
                Real.mul_rpow (by norm_num) (abs_nonneg A)]
            have e2 : (3 : ℝ) ^ p = (3 : ℝ) ^ (p - 1) * 3 := by
              rw [← Real.rpow_add_one (by norm_num)]; ring_nf
            rw [e1, e2]; ring
    refine le_trans (eLpNorm_le_of_lint hp hK hint) ?_
    apply ENNReal.ofReal_le_ofReal
    have hu2 : u ^ 2 ≤ ((m : ℝ) * t) ^ 2 := by
      apply pow_le_pow_left₀ hu0 hut
    have h12 : 3 * M ≤ max 12 (3 * M) := le_max_right _ _
    have hA := abs_nonneg A
    calc 3 * |A| * (M * u ^ 2) = (3 * M) * |A| * u ^ 2 := by ring
      _ ≤ max 12 (3 * M) * |A| * ((m : ℝ) * t) ^ 2 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right h12 hA
          · exact hu2
          · positivity
          · positivity


/-! ## Termos geométricos da série de Besov -/

/-- Termo `m^{-s} 2^{r s} min{1, (m/2^r)^2}`. -/
noncomputable def aTerm (s : ℝ) (m r : ℕ) : ℝ :=
  (m : ℝ) ^ (-s) * (2 : ℝ) ^ ((r : ℝ) * s) * min 1 (((m : ℝ) * (1 / (2 : ℝ) ^ r)) ^ 2)

lemma aTerm_nonneg (s : ℝ) (m r : ℕ) : 0 ≤ aTerm s m r := by
  unfold aTerm; positivity

lemma aTerm_le_low {s : ℝ} (hs0 : 0 < s) {m : ℕ} (hm : 1 ≤ m) {r : ℕ}
    (hr : r ≤ Nat.log 2 m) :
    aTerm s m r ≤ ((2 : ℝ) ^ (-s)) ^ (Nat.log 2 m - r) := by
  set k := Nat.log 2 m with hk
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmk : (2 : ℝ) ^ k ≤ m := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h1 : min 1 (((m : ℝ) * (1 / (2 : ℝ) ^ r)) ^ 2) ≤ 1 := min_le_left _ _
  have h0 : 0 ≤ (m : ℝ) ^ (-s) * (2 : ℝ) ^ ((r : ℝ) * s) := by positivity
  have h2 : (m : ℝ) ^ (-s) ≤ ((2 : ℝ) ^ k) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hmk (by linarith)
  have h3 : ((2 : ℝ) ^ k) ^ (-s) * (2 : ℝ) ^ ((r : ℝ) * s)
      = ((2 : ℝ) ^ (-s)) ^ (k - r) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-s)) (k - r), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    rw [Nat.cast_sub hr]; ring
  unfold aTerm
  calc (m : ℝ) ^ (-s) * (2 : ℝ) ^ ((r : ℝ) * s) * min 1 (((m : ℝ) * (1 / (2 : ℝ) ^ r)) ^ 2)
      ≤ (m : ℝ) ^ (-s) * (2 : ℝ) ^ ((r : ℝ) * s) * 1 :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = (m : ℝ) ^ (-s) * (2 : ℝ) ^ ((r : ℝ) * s) := mul_one _
    _ ≤ ((2 : ℝ) ^ k) ^ (-s) * (2 : ℝ) ^ ((r : ℝ) * s) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := h3

lemma aTerm_le_high {s : ℝ} (hs2 : s < 2) {m : ℕ} (hm : 1 ≤ m) {r : ℕ}
    (hr : Nat.log 2 m < r) :
    aTerm s m r ≤ ((2 : ℝ) ^ (-(2 - s))) ^ (r - Nat.log 2 m - 1) := by
  set k := Nat.log 2 m with hk
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmlt : (m : ℝ) < (2 : ℝ) ^ (k + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) m
  have hE : 0 < 2 - s := by linarith
  have h1 : min 1 (((m : ℝ) * (1 / (2 : ℝ) ^ r)) ^ 2) ≤ ((m : ℝ) * (1 / (2 : ℝ) ^ r)) ^ 2 :=
    min_le_right _ _
  have h0 : 0 ≤ (m : ℝ) ^ (-s) * (2 : ℝ) ^ ((r : ℝ) * s) := by positivity
  -- passo A: identidade algébrica
  have hA : (m : ℝ) ^ (-s) * (2 : ℝ) ^ ((r : ℝ) * s) * ((m : ℝ) * (1 / (2 : ℝ) ^ r)) ^ 2
      = (m : ℝ) ^ (2 - s) * ((2 : ℝ) ^ (-(2 - s))) ^ r := by
    have e1 : (m : ℝ) ^ (-s) * (m : ℝ) ^ (2 : ℕ) = (m : ℝ) ^ (2 - s) := by
      rw [← Real.rpow_natCast (m : ℝ) 2, ← Real.rpow_add hmpos]; push_cast; ring_nf
    have e2 : (2 : ℝ) ^ ((r : ℝ) * s) * (1 / (2 : ℝ) ^ r) ^ 2
        = ((2 : ℝ) ^ (-(2 - s))) ^ r := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(2 - s))) r, ← Real.rpow_mul (by norm_num)]
      have : (1 / (2 : ℝ) ^ r) ^ 2 = (2 : ℝ) ^ (-(2 * (r : ℝ))) := by
        rw [one_div, inv_pow, ← Real.rpow_natCast (2 : ℝ) r,
          ← Real.rpow_natCast ((2 : ℝ) ^ (r : ℝ)) 2, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_neg (by norm_num)]
        push_cast; ring_nf
      rw [this, ← Real.rpow_add (by norm_num)]
      congr 1; ring
    calc (m : ℝ) ^ (-s) * (2 : ℝ) ^ ((r : ℝ) * s) * ((m : ℝ) * (1 / (2 : ℝ) ^ r)) ^ 2
        = ((m : ℝ) ^ (-s) * (m : ℝ) ^ (2 : ℕ)) *
            ((2 : ℝ) ^ ((r : ℝ) * s) * (1 / (2 : ℝ) ^ r) ^ 2) := by ring
      _ = _ := by rw [e1, e2]
  -- passo B: `m^{2-s} ≤ (2^{k+1})^{2-s}`
  have hB : (m : ℝ) ^ (2 - s) ≤ ((2 : ℝ) ^ (k + 1)) ^ (2 - s) :=
    Real.rpow_le_rpow hmpos.le hmlt.le hE.le
  have hC : ((2 : ℝ) ^ (k + 1)) ^ (2 - s) * ((2 : ℝ) ^ (-(2 - s))) ^ r
      = ((2 : ℝ) ^ (-(2 - s))) ^ (r - k - 1) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(2 - s))) r,
      ← Real.rpow_natCast ((2 : ℝ) ^ (-(2 - s))) (r - k - 1),
      ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (2 : ℝ) (k + 1), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    have : ((r - k - 1 : ℕ) : ℝ) = (r : ℝ) - k - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [this]; push_cast; ring
  unfold aTerm
  calc (m : ℝ) ^ (-s) * (2 : ℝ) ^ ((r : ℝ) * s) * min 1 (((m : ℝ) * (1 / (2 : ℝ) ^ r)) ^ 2)
      ≤ (m : ℝ) ^ (-s) * (2 : ℝ) ^ ((r : ℝ) * s) * ((m : ℝ) * (1 / (2 : ℝ) ^ r)) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = (m : ℝ) ^ (2 - s) * ((2 : ℝ) ^ (-(2 - s))) ^ r := hA
    _ ≤ ((2 : ℝ) ^ (k + 1)) ^ (2 - s) * ((2 : ℝ) ^ (-(2 - s))) ^ r :=
        mul_le_mul_of_nonneg_right hB (by positivity)
    _ = _ := hC


/-! ## Série de Besov e normalização -/

lemma pow2_pow_rpow (c Q : ℝ) (n : ℕ) :
    (((2 : ℝ) ^ (-c)) ^ n) ^ Q = ((2 : ℝ) ^ (-(c * Q))) ^ n := by
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-c) := Real.rpow_nonneg (by norm_num) _
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-c)) n, ← Real.rpow_mul h2,
    ← Real.rpow_natCast ((2 : ℝ) ^ (-(c * Q))) n, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num)]
  congr 1; ring

lemma aTerm_le_one {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    aTerm s m r ≤ 1 := by
  by_cases hr : r ≤ Nat.log 2 m
  · refine le_trans (aTerm_le_low hs0 hm hr) ?_
    apply pow_le_one₀ (by positivity)
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  · push_neg at hr
    refine le_trans (aTerm_le_high hs2 hm hr) ?_
    apply pow_le_one₀ (by positivity)
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)

/-- Cada termo da série de Besov da soma de bumps, em função de `aTerm`. -/
lemma besovSeq_Fm_le {K0 : ℝ}
    (hmod : ∀ {p : ℝ}, 1 ≤ p → ∀ {m : ℕ}, 1 ≤ m → ∀ (A t : ℝ), 0 < t →
      wtP (ENNReal.ofReal p) t (Fm m A) ≤
        ENNReal.ofReal (K0 * |A| * min 1 ((m * t) ^ 2)))
    {p s : ℝ} (hp : 1 ≤ p) {m : ℕ} (hm : 1 ≤ m) {b : ℝ} (hb : 0 ≤ b) (r : ℕ) :
    FormalizacaoRed.besovSeq (ENNReal.ofReal p) s (Fm m (b * (m : ℝ) ^ (-s))) r
      ≤ ENNReal.ofReal (K0 * b * aTerm s m r) := by
  unfold FormalizacaoRed.besovSeq
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hA : |b * (m : ℝ) ^ (-s)| = b * (m : ℝ) ^ (-s) :=
    abs_of_nonneg (by positivity)
  calc ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r)
        (Fm m (b * (m : ℝ) ^ (-s)))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) * ENNReal.ofReal
          (K0 * |b * (m : ℝ) ^ (-s)| * min 1 (((m : ℝ) * (1 / (2 : ℝ) ^ r)) ^ 2)) :=
        mul_le_mul_right (hmod hp hm _ _ (by positivity)) _
    _ = ENNReal.ofReal (K0 * b * aTerm s m r) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hA]; unfold aTerm; ring

/-- Cota `ℓ^q` uniforme para a soma de bumps. -/
lemma exists_Lq {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) {q : ℝ≥0∞} (hq : 0 < q) {K0 : ℝ}
    (hK0 : 0 < K0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {p : ℝ}, 1 ≤ p →
      (∀ {p : ℝ}, 1 ≤ p → ∀ {m : ℕ}, 1 ≤ m → ∀ (A t : ℝ), 0 < t →
        wtP (ENNReal.ofReal p) t (Fm m A) ≤
          ENNReal.ofReal (K0 * |A| * min 1 ((m * t) ^ 2))) →
      ∀ {m : ℕ}, 1 ≤ m → ∀ {b : ℝ}, 0 ≤ b →
        lqNorm q (FormalizacaoRed.besovSeq (ENNReal.ofReal p) s (Fm m (b * (m : ℝ) ^ (-s))))
          ≤ ENNReal.ofReal (b * L) := by
  by_cases hqt : q = ⊤
  · refine ⟨K0, hK0.le, ?_⟩
    intro p hp hmod m hm b hb
    unfold lqNorm
    rw [if_pos hqt]
    refine iSup_le (fun r => ?_)
    refine le_trans (besovSeq_Fm_le hmod hp hm hb r) ?_
    apply ENNReal.ofReal_le_ofReal
    have := aTerm_le_one hs0 hs2 hm r
    have h0 : 0 ≤ K0 * b := by positivity
    nlinarith [aTerm_nonneg s m r]
  · set Q := q.toReal with hQ
    have hQpos : 0 < Q := ENNReal.toReal_pos hq.ne' hqt
    set α : ℝ := (2 : ℝ) ^ (-(s * Q)) with hα
    set β : ℝ := (2 : ℝ) ^ (-((2 - s) * Q)) with hβ
    have hα0 : 0 ≤ α := by positivity
    have hβ0 : 0 ≤ β := by positivity
    have hα1 : α < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
    have hβ1 : β < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
    set D : ℝ := 1 / (1 - α) + 1 / (1 - β) with hD
    have hD0 : 0 ≤ D := by
      rw [hD]; apply add_nonneg <;> apply div_nonneg <;> linarith
    refine ⟨K0 * D ^ Q⁻¹, by positivity, ?_⟩
    intro p hp hmod m hm b hb
    have hsum : ∑' r, ENNReal.ofReal (aTerm s m r ^ Q) ≤ ENNReal.ofReal D := by
      refine tsum_split_le hα0 hα1 hβ0 hβ1 (Nat.log 2 m) (fun r => aTerm s m r ^ Q) ?_
      intro r
      refine ⟨Real.rpow_nonneg (aTerm_nonneg s m r) _, ?_⟩
      by_cases hr : r ≤ Nat.log 2 m
      · have h1 := Real.rpow_le_rpow (aTerm_nonneg s m r) (aTerm_le_low hs0 hm hr) hQpos.le
        rw [pow2_pow_rpow] at h1
        have : ¬ Nat.log 2 m < r := by omega
        simp only [if_pos hr, if_neg this, add_zero]
        exact h1
      · push_neg at hr
        have h1 := Real.rpow_le_rpow (aTerm_nonneg s m r) (aTerm_le_high hs2 hm hr) hQpos.le
        rw [pow2_pow_rpow] at h1
        have : ¬ r ≤ Nat.log 2 m := by omega
        simp only [if_pos hr, if_neg this, zero_add]
        exact h1
    have := lqNorm_le_of_pow_sum hq hqt
      (FormalizacaoRed.besovSeq (ENNReal.ofReal p) s (Fm m (b * (m : ℝ) ^ (-s)))) (c := K0 * b)
      (by positivity) (fun r => aTerm s m r) (fun r => aTerm_nonneg s m r)
      (fun r => besovSeq_Fm_le hmod hp hm hb r) hD0 hsum
    convert this using 2
    ring

/-- **Normalização do empacotamento.** Existe `b = b(s,q) > 0`, independente de `m ≥ 1` e de
`p ≥ 1`, tal que a soma de `m` bumps de amplitude `b m^{-s}` tem `‖·‖*_{B^s_{p,q}} ≤ 1`. -/
theorem packing_norm_le {p s : ℝ} (hp : 1 ≤ p) (hs0 : 0 < s) (hs2 : s < 2) {q : ℝ≥0∞}
    (hq : 0 < q) :
    ∃ b : ℝ, 0 < b ∧ ∀ m : ℕ, 1 ≤ m →
      FormalizacaoLow.besovNorm (ENNReal.ofReal p) s q
        (Fm m (b * (m : ℝ) ^ (-s))) ≤ 1 := by
  obtain ⟨K0, hK0, hmod⟩ := exists_K0
  obtain ⟨L, hL0, hL⟩ := exists_Lq hs0 hs2 hq hK0
  refine ⟨1 / (1 + L), by positivity, ?_⟩
  intro m hm
  set b : ℝ := 1 / (1 + L) with hb
  have hb0 : 0 ≤ b := by positivity
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (m : ℝ) ^ (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm) (by linarith)
  unfold FormalizacaoLow.besovNorm
  have h1 := eLpNorm_Fm_le hp m (b * (m : ℝ) ^ (-s))
  have h2 := hL hp hmod hm hb0
  have habs : |b * (m : ℝ) ^ (-s)| ≤ b := by
    rw [abs_of_nonneg (by positivity)]
    calc b * (m : ℝ) ^ (-s) ≤ b * 1 := mul_le_mul_of_nonneg_left hm1 hb0
      _ = b := mul_one _
  calc eLpNorm (Fm m (b * (m : ℝ) ^ (-s))) (ENNReal.ofReal p) vol01 +
        lqNorm q (FormalizacaoRed.besovSeq (ENNReal.ofReal p) s (Fm m (b * (m : ℝ) ^ (-s))))
      ≤ ENNReal.ofReal b + ENNReal.ofReal (b * L) :=
        add_le_add (h1.trans (ENNReal.ofReal_le_ofReal habs)) h2
    _ = ENNReal.ofReal (b + b * L) := (ENNReal.ofReal_add hb0 (by positivity)).symm
    _ = 1 := by
        have : b + b * L = 1 := by
          rw [hb]; field_simp
        rw [this, ENNReal.ofReal_one]


end FormalizacaoPacking
