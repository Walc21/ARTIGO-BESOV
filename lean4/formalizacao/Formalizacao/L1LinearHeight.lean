import Formalizacao.AlturaCritical2
import Formalizacao.NodalVariable
import Formalizacao.UnifSup

/-!
# Altura linear em `B¹_{1,q}`

A média dos valores nodais do quase-interpolante é controlada pela norma em `L¹`.
Com a quantização por nó, isso fornece a taxa de `lp:prop:l1-linear-height` para todo `q > 0`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace FormalizacaoAltura

open FormalizacaoGrid FormalizacaoLp FormalizacaoLow FormalizacaoCor FormalizacaoCrit

private lemma cell_subset_unit {n j : ℕ} (hn : 1 ≤ n) (hj : j < n) :
    cell n j ⊆ Icc (0 : ℝ) 1 := by
  have ht := FormalizacaoW.tn_n hn
  exact Icc_subset_Icc (by unfold tn; positivity) (ht ▸ tn_mono n hj)

/-- Os valores nodais são limitados pela massa local. Na soma, somente a célula final
pode contribuir duas vezes. -/
private lemma nodal_l1_bounds {n : ℕ} (hn : 1 ≤ n) {f : ℝ → ℝ}
    (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1)) :
    (∀ j ≤ n, |lam n f j| ≤ 4 * n * (Np 1 f (Icc 0 1)).toReal) ∧
      (∑ j ∈ Finset.range (n + 1), |lam n f j|) ≤ 8 * n * (Np 1 f (Icc 0 1)).toReal := by
  let M (s : Set ℝ) : ℝ := (Np 1 f s).toReal
  have hM {s : Set ℝ} (hs : s ⊆ Icc 0 1) : M s = ∫ x in s, |f x| := by
    have hi : IntegrableOn f s := hfi.mono_set hs
    simp only [M, Np, ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm]
    rw [← ofReal_integral_norm_eq_lintegral_enorm hi, ENNReal.toReal_ofReal (integral_nonneg
      (fun x ↦ norm_nonneg (f x)))]
    simp only [Real.norm_eq_abs]
  have hfiAbs : IntegrableOn (fun x ↦ |f x|) (Icc 0 1) := hfi.abs
  have hcomp {s : Set ℝ} (hs : s ⊆ Icc 0 1) : M s ≤ M (Icc 0 1) := by
    rw [hM hs, hM Subset.rfl]
    exact integral_mono_measure (Measure.restrict_mono hs le_rfl)
      (ae_of_all _ fun x ↦ abs_nonneg (f x)) hfiAbs
  have hlocal : ∀ j ≤ n, |lam n f j| ≤ 4 * n * M (cell n (cellIdx n j)) := by
    intro j hj
    have hc : cellIdx n j < n := by unfold cellIdx; omega
    have hi : IntegrableOn f (cell n (cellIdx n j)) := hfi.mono_set (cell_subset_unit hn hc)
    have hfin := (memLp_one_iff_integrable.mpr hi).eLpNorm_lt_top
    have h := abs_lam_le hn (p := 1) (by norm_num) j hj hf (by simpa using hfin)
    simpa [M, Np] using h
  refine ⟨fun j hj ↦ (hlocal j hj).trans ?_, ?_⟩
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hcomp (cell_subset_unit hn (by unfold cellIdx; omega))
  · have hsum : (∑ j ∈ Finset.range n, M (cell n j)) = M (Icc 0 1) := by
      have hθ (j : ℕ) : tn n j ≤ tn n (j + 1) := tn_mono n (Nat.le_succ _)
      have hcell (j : ℕ) (hj : j < n) :
          M (cell n j) = ∫ x in tn n j..tn n (j + 1), |f x| := by
        rw [hM (cell_subset_unit hn hj)]
        exact (integral_Icc_eq_integral_Ioc.trans (intervalIntegral.integral_of_le (hθ j)).symm)
      have hint (j : ℕ) (hj : j < n) : IntervalIntegrable (fun x ↦ |f x|) volume
          (tn n j) (tn n (j + 1)) :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le (hθ j)).mpr
          (hfiAbs.mono_set (cell_subset_unit hn hj))
      have h₀ : tn n 0 = 0 := by simp [tn]
      have h₁ := FormalizacaoW.tn_n hn
      calc
        _ = ∑ j ∈ Finset.range n, ∫ x in tn n j..tn n (j + 1), |f x| :=
          Finset.sum_congr rfl fun j hj ↦ hcell j (Finset.mem_range.mp hj)
        _ = _ := by
          rw [intervalIntegral.sum_integral_adjacent_intervals hint, h₀, h₁, hM Subset.rfl,
            intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
    have hidx (j : ℕ) (hj : j < n) : cellIdx n j = j := min_eq_left (by omega)
    have hlast : M (cell n (cellIdx n n)) ≤ M (Icc 0 1) :=
      hcomp (cell_subset_unit hn (by unfold cellIdx; omega))
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), (4 * n * M (cell n (cellIdx n j))) :=
        Finset.sum_le_sum fun j hj ↦ hlocal j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      _ = 4 * n * (M (Icc 0 1) + M (cell n (cellIdx n n))) := by
        rw [← Finset.mul_sum, Finset.sum_range_succ, ← hsum]
        congr 2
        exact Finset.sum_congr rfl fun j hj ↦ by rw [hidx j (Finset.mem_range.mp hj)]
      _ ≤ 4 * n * (M (Icc 0 1) + M (Icc 0 1)) := by gcongr
      _ = _ := by ring

private lemma Q_two_l1_le {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1)) :
    ∀ x ∈ Icc (0 : ℝ) 1, |Q 2 f x| ≤ 8 * (Np 1 f (Icc 0 1)).toReal := by
  intro x hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp (unit_subset_cells (n := 2) (by decide) hx)
  have hnode := (nodal_l1_bounds (n := 2) (by decide) hf hfi).1
  have hn : (1 : ℕ) ≤ 2 := by decide
  rw [Q_cell hn j.isLt f hj, hat_left_of_mem hn hj, hat_right_of_mem hn hj]
  let L := (tn 2 ((j : ℕ) + 1) - x) * (2 : ℝ)
  let R := (x - tn 2 j) * (2 : ℝ)
  have hL : 0 ≤ L :=
    mul_nonneg (sub_nonneg.mpr hj.2) (by norm_num)
  have hR : 0 ≤ R := mul_nonneg (sub_nonneg.mpr hj.1) (by norm_num)
  change |lam 2 f j * L + lam 2 f ((j : ℕ) + 1) * R| ≤ _
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul (lam 2 f j) L, abs_mul (lam 2 f ((j : ℕ) + 1)) R,
    abs_of_nonneg hL, abs_of_nonneg hR]
  have h₀ := mul_le_mul_of_nonneg_right (hnode j j.isLt.le) hL
  have h₁ := mul_le_mul_of_nonneg_right (hnode ((j : ℕ) + 1) j.isLt) hR
  refine (add_le_add h₀ h₁).trans (le_of_eq ?_)
  dsimp [L, R]
  rw [tn_succ _ _ hn]
  norm_num
  ring

private lemma l1_nodal_jump {CW B : ℝ} (hCW : 0 ≤ CW) (hW : WhitneyLp 1 CW)
    {q : ℝ≥0∞} (hq : 0 < q) (hB : 0 ≤ B) {f : ℝ → ℝ} (hf : Measurable f)
    (hfi : IntegrableOn f (Icc 0 1)) (hfin : Np 1 f (Icc 0 1) < ⊤)
    (hball : besovNorm 1 1 q f ≤ ENNReal.ofReal B)
    {r : ℕ} (hr : 1 ≤ r) {j : ℕ} (hj : j < 2 ^ r) :
    |lam (2 ^ r) f (j + 1) - lam (2 ^ r) f j| ≤ (32 + 576 * CW) * B := by
  let K (k : ℕ) : ℝ := 288 * CW * B * (2 : ℝ) ^ (k + 1)
  have hp : (1 : ℝ) ≤ 1 := le_rfl
  have hx (k : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) * 1)) *
      wtP (ENNReal.ofReal 1) (1 / (2 : ℝ) ^ k) f ≤ ENNReal.ofReal B := by
    rw [← FormalizacaoRed.besovSeq, ENNReal.ofReal_one]
    exact (FormalizacaoCrit2.term_le_lqNorm hq _ k).trans
      ((lqNorm_le_besovNorm _ _ _ _).trans hball)
  have hK (k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : i < 2 ^ (k + 1)) :
      ∃ α β : ℝ, |β| ≤ K k ∧ ∀ x ∈ cell (2 ^ (k + 1)) i,
        Q (2 ^ (k + 1)) f x - Q (2 ^ k) f x = α + β * x := by
    obtain ⟨β, hβ, α, hα⟩ := FormalizacaoL55b.vk_slope_le hp hW hCW hf hfi hfin
      ENNReal.ofReal_lt_top hx hk hi
    refine ⟨α, β, hβ.trans ?_, hα⟩
    rw [ENNReal.toReal_ofReal hB]
    norm_num [K, pow_succ, ← Real.rpow_natCast]
    ring_nf
    exact le_rfl
  have hnorm : (Np 1 f (Icc 0 1)).toReal ≤ B :=
    (ball_bounds hp hq hB hf (by simpa using hball)).1
  have hsup (x : ℝ) (hx : x ∈ Icc 0 1) : |Q 2 f x| ≤ 8 * B :=
    (Q_two_l1_le hf hfi x hx).trans (by linarith)
  have h := nodal_jump hsup K hK hr hj
  have hn : (1 : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow (n := r)
  have hn0 : 0 < ((2 ^ r : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hbase : 4 * (8 * B) / ((2 ^ r : ℕ) : ℝ) ≤ 32 * B := by
    rw [div_le_iff₀ hn0]
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hn)]
  have hsum : (∑ k ∈ Finset.Ico 1 r, K k / ((2 ^ r : ℕ) : ℝ)) ≤ 576 * CW * B := by
    rw [← Finset.sum_div, div_le_iff₀ hn0]
    simp only [K, ← Finset.mul_sum, Nat.cast_pow, Nat.cast_ofNat]
    calc _ ≤ (288 * CW * B) * (2 * (2 : ℝ) ^ r) :=
            mul_le_mul_of_nonneg_left (sum_pow_two_le r) (by positivity)
      _ = _ := by ring
  linarith only [h, hbase, hsum]

/-- Altura linear em `B¹_{1,q}`, com a constante escolhida antes da bola, de `q` e da escala. -/
theorem l1_linear_height :
    ∃ CW CE : ℝ, 0 ≤ CW ∧ 1 ≤ CE ∧ ∀ q : ℝ≥0∞, 0 < q →
      ∀ B : ℝ, 1 ≤ B → ∀ f : ℝ → ℝ, Measurable f →
      besovNorm 1 1 q f ≤ ENNReal.ofReal B →
      ∀ r : ℕ, 1 ≤ r → ∀ H : ℕ, CE * (B + 1) * (2 : ℝ) ^ r ≤ H →
      ∃ g ∈ classNH (2 ^ r) H, distP 1 f g ≤
        9 * ENNReal.ofReal CW * wtP 1 (1 / (2 : ℝ) ^ r) f +
          ENNReal.ofReal (CE * (B + 1) / H) := by
  obtain ⟨CW, hCW, hW⟩ := FormalizacaoW.whitney_lp (p := 1) le_rfl
  let CJ := 32 + 576 * CW
  let CE := 320 + 64 * CJ
  have hCJ : 0 ≤ CJ := by dsimp [CJ]; positivity
  have hCE : 1 ≤ CE := by dsimp [CE]; linarith
  refine ⟨CW, CE, hCW, hCE, fun q hq B hB f hf hball r hr H hH ↦ ?_⟩
  let n : ℕ := 2 ^ r
  let J := CJ * B
  have hn : 2 ≤ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ n := Nat.pow_le_pow_right (by decide) hr
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcast : (n : ℝ) = (2 : ℝ) ^ r := by simp [n]
  rw [← hcast] at hH
  have hHpos : (0 : ℝ) < H :=
    lt_of_lt_of_le (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) hH
  have hJ : 0 ≤ J := mul_nonneg hCJ (by linarith)
  have hp : (1 : ℝ) ≤ 1 := le_rfl
  obtain ⟨hBf, _, _, hfin, _, _⟩ :=
    ball_bounds (s := 1) (B := B) hp hq (by linarith) hf (by simpa using hball)
  have hmem : MemLp f 1 vol01 := ⟨hf.aestronglyMeasurable, by simpa [Np] using hfin⟩
  have hfi : IntegrableOn f (Icc 0 1) := memLp_one_iff_integrable.mp hmem
  have ⟨hnodes, hsum⟩ := nodal_l1_bounds (n := n) (by omega) hf hfi
  have hmax (j : ℕ) (hj : j ≤ n) : |lam n f j| ≤ 4 * n * B :=
    (hnodes j hj).trans (mul_le_mul_of_nonneg_left hBf (by positivity))
  have havg : (∑ j ∈ Finset.range (n + 1), |lam n f j|) ≤ 8 * n * B :=
    hsum.trans (mul_le_mul_of_nonneg_left hBf (by positivity))
  have hjump : ∀ j < n, |lam n f (j + 1) - lam n f j| ≤ J := by
    intro j hj
    exact l1_nodal_jump hCW hW hq (by linarith) hf hfi hfin hball hr hj
  have hHnode (j : ℕ) (hj : j ≤ n) : 8 * (1 + J + |lam n f j|) ≤ (H : ℝ) := by
    have hscale : 1 + J ≤ (1 + J) * (n : ℝ) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    calc
      _ ≤ 8 * (1 + J + 4 * n * B) := by linarith [hmax j hj]
      _ ≤ (8 + 8 * J + 32 * B) * n := by linarith [hscale]
      _ ≤ CE * (B + 1) * n := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [CE, J]
        nlinarith [mul_nonneg hCJ (show 0 ≤ B by linarith)]
      _ ≤ H := hH
  have hHjump : (n : ℝ) * (J + 4) ≤ H := by
    refine le_trans ?_ hH
    rw [mul_comm (n : ℝ)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp [CE, J]
    nlinarith [mul_nonneg hCJ (show 0 ≤ B by linarith)]
  have hu (j : ℕ) (hj : j < n) (x : ℝ) (hx : x ∈ cell n j) :
      Q n f x = (1 - (n : ℝ) * (x - tn n j)) * lam n f j +
        (n : ℝ) * (x - tn n j) * lam n f (j + 1) := by
    have hn₁ : 1 ≤ n := by omega
    rw [Q_cell hn₁ hj f hx, hat_left_of_mem hn₁ hx, hat_right_of_mem hn₁ hx, tn_succ _ _ hn₁]
    have hn₀ : (n : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hcast] at hHjump
  obtain ⟨g, hg, _, hquant⟩ := nodal_variable_height hr hJ (lam n f) hjump hHnode hHjump
    (Q n f) (by simpa only [← hcast] using hu)
  refine ⟨g, hg, ?_⟩
  have hQm := (FormalizacaoL55.Q_continuous n f).measurable
  have hgm : Measurable g := by
    obtain ⟨T, _, rfl⟩ := hg
    exact measurable_eval T 0 0
  have htri : distP 1 f g ≤ distP 1 f (Q n f) + distP 1 (Q n f) g := by
    unfold distP
    have he : f - g = (f - Q n f) + (Q n f - g) := by abel
    rw [he]
    exact eLpNorm_add_le (hf.sub hQm).aestronglyMeasurable
      (hQm.sub hgm).aestronglyMeasurable le_rfl
  have hQ : distP 1 f (Q n f) ≤ 9 * ENNReal.ofReal CW * wtP 1 (1 / (2 : ℝ) ^ r) f := by
    simpa [distP, Np, hcast] using quasi_error hp hW hn hf hfi hfin
  refine htri.trans (add_le_add hQ (hquant.trans (ENNReal.ofReal_le_ofReal ?_)))
  rw [← hcast]
  have hsumw : (∑ j ∈ Finset.range (n + 1), (1 + J + |lam n f j|)) ≤
      (2 * (1 + J) + 8 * B) * n := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
    have hcard : (n : ℝ) + 1 ≤ 2 * n := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hcard (show 0 ≤ 1 + J by positivity)]
  have hCE' : 32 * (2 * (1 + J) + 8 * B) ≤ CE * (B + 1) := by
    dsimp [CE, J]
    nlinarith [mul_nonneg hCJ (show 0 ≤ B by linarith)]
  calc
    _ ≤ 32 / ((H : ℝ) * n) * ((2 * (1 + J) + 8 * B) * n) :=
      mul_le_mul_of_nonneg_left hsumw (by positivity)
    _ = 32 * (2 * (1 + J) + 8 * B) / H := by
      have hn₀ : (n : ℝ) ≠ 0 := by positivity
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hCE' hHpos.le

end FormalizacaoAltura
