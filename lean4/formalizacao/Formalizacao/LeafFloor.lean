import Formalizacao.Packing
import Formalizacao.AlturaSlope
import Formalizacao.AlturaNecessity

/-!
# F2.3 — Piso pelo número de folhas (`lp:lem:leaf-budget-floor`)

Parte 1: combinatória das árvores. Os pontos de divisão (`splits`) de uma árvore com `L` folhas
são no máximo `L - 1`; fora dos pontos de divisão, `T.eval` é afim em todo intervalo aberto.
-/

open scoped ENNReal
open MeasureTheory Set Finset Artigo

namespace FormalizacaoLeaf

open FormalizacaoPacking FormalizacaoAltura FormalizacaoLp

/-- Pontos de divisão (pontos médios dos nós internos) da árvore enraizada em `J_{k,m}`. -/
noncomputable def splits : ℕ → ℤ → LTree → Finset ℝ
  | _, _, LTree.leaf _ => ∅
  | k, m, LTree.node l r =>
      insert (cL (k + 1) (2 * m + 1)) (splits (k + 1) (2 * m) l ∪ splits (k + 1) (2 * m + 1) r)

lemma card_splits_le : ∀ (T : LTree) (k : ℕ) (m : ℤ), (splits k m T).card + 1 ≤ T.numLeaves := by
  intro T
  induction T with
  | leaf a => intro k m; simp [splits, LTree.numLeaves, LTree.leaves]
  | node l r ihl ihr =>
    intro k m
    rw [LTree.numLeaves_node]
    have h1 := ihl (k + 1) (2 * m)
    have h2 := ihr (k + 1) (2 * m + 1)
    simp only [splits]
    have h3 : (insert (cL (k + 1) (2 * m + 1))
        (splits (k + 1) (2 * m) l ∪ splits (k + 1) (2 * m + 1) r)).card
        ≤ (splits (k + 1) (2 * m) l ∪ splits (k + 1) (2 * m + 1) r).card + 1 :=
      Finset.card_insert_le _ _
    have h4 := Finset.card_union_le (splits (k + 1) (2 * m) l) (splits (k + 1) (2 * m + 1) r)
    omega

lemma splits_node_left (l r : LTree) (k : ℕ) (m : ℤ) :
    splits (k + 1) (2 * m) l ⊆ splits k m (LTree.node l r) := by
  intro x hx
  simp only [splits, Finset.mem_insert, Finset.mem_union]
  exact Or.inr (Or.inl hx)

lemma splits_node_right (l r : LTree) (k : ℕ) (m : ℤ) :
    splits (k + 1) (2 * m + 1) r ⊆ splits k m (LTree.node l r) := by
  intro x hx
  simp only [splits, Finset.mem_insert, Finset.mem_union]
  exact Or.inr (Or.inr hx)

/-- Em todo intervalo aberto contido na célula raiz e sem pontos de divisão, `T.eval` é afim. -/
lemma affine_on_open : ∀ (T : LTree) (k : ℕ) (m : ℤ) (c d : ℝ), LTree.WF k m T →
    Ioo c d ⊆ cellIcc k m → (∀ x ∈ splits k m T, x ∉ Ioo c d) →
    ∃ α β : ℝ, ∀ x ∈ Ioo c d, T.eval k m x = α + β * x := by
  intro T
  induction T with
  | leaf a =>
    intro k m c d _ _ _
    refine ⟨(a.y0 : ℝ) - (a.s : ℝ) * (a.x0 : ℝ), (a.s : ℝ), fun x _ => ?_⟩
    simp only [LTree.eval, Atom.eval]
    ring
  | node l r ihl ihr =>
    intro k m c d hWF hsub hns
    have hμ : cL (k + 1) (2 * m + 1) ∉ Ioo c d :=
      hns _ (by simp only [splits]; exact Finset.mem_insert_self _ _)
    by_cases hd : d ≤ cL (k + 1) (2 * m + 1)
    · have hsubl : Ioo c d ⊆ cellIcc (k + 1) (2 * m) := by
        intro x hx
        have h1 := hsub hx
        rw [cellIcc_eq] at h1 ⊢
        refine ⟨?_, ?_⟩
        · rw [cL_child_left]; exact h1.1
        · rw [cR_child_left]; linarith [hx.2]
      obtain ⟨α, β, h⟩ := ihl (k + 1) (2 * m) c d hWF.1 hsubl
        (fun x hx => hns x (splits_node_left l r k m hx))
      refine ⟨α, β, fun x hx => ?_⟩
      have hlt : x < cL (k + 1) (2 * m + 1) := lt_of_lt_of_le hx.2 hd
      simp only [LTree.eval, if_pos hlt]
      exact h x hx
    · push_neg at hd
      have hc : cL (k + 1) (2 * m + 1) ≤ c := by
        by_contra hcon
        push_neg at hcon
        exact hμ ⟨hcon, hd⟩
      have hsubr : Ioo c d ⊆ cellIcc (k + 1) (2 * m + 1) := by
        intro x hx
        have h1 := hsub hx
        rw [cellIcc_eq] at h1 ⊢
        refine ⟨?_, ?_⟩
        · linarith [hx.1]
        · rw [cR_child_right]; exact h1.2
      obtain ⟨α, β, h⟩ := ihr (k + 1) (2 * m + 1) c d hWF.2.1 hsubr
        (fun x hx => hns x (splits_node_right l r k m hx))
      refine ⟨α, β, fun x hx => ?_⟩
      have hnlt : ¬ x < cL (k + 1) (2 * m + 1) := by
        have := hx.1; push_neg; linarith
      simp only [LTree.eval, if_neg hnlt]
      exact h x hx

/-- Contagem de células afins: com `m = 2N`, todo `g ∈ Σ_{N,H}` é afim no interior de pelo menos
`N` células de teste `(j/m, (j+1)/m)`, `j < m`. Vale para árvores adaptativas arbitrárias. -/
lemma exists_good_cells {g : ℝ → ℝ} {N H : ℕ} (hN : 1 ≤ N)
    (hg : g ∈ Pendencias.Agenda.Sigma (fun _ => H) N) :
    ∃ G : Finset ℕ, N ≤ G.card ∧ (∀ j ∈ G, j < 2 * N) ∧
      ∀ j ∈ G, ∃ α β : ℝ, ∀ x ∈ Ioo ((j : ℝ) / (2 * N : ℕ)) (((j : ℝ) + 1) / (2 * N : ℕ)),
        g x = α + β * x := by
  simp only [Pendencias.Agenda.Sigma, Set.mem_setOf_eq] at hg
  rcases hg with rfl | ⟨T, hadm, rfl⟩
  · refine ⟨Finset.range (2 * N), ?_, fun j hj => Finset.mem_range.mp hj, fun j _ => ⟨0, 0, ?_⟩⟩
    · simp; omega
    · intro x _; simp
  · obtain ⟨hWF, hleaf, _⟩ := hadm
    set m : ℕ := 2 * N with hm
    have hmpos : (0 : ℝ) < m := by
      have : 0 < m := by omega
      exact_mod_cast this
    set S := splits 0 0 T with hS
    have hcard : S.card + 1 ≤ N := le_trans (card_splits_le T 0 0) hleaf
    set bad : Finset ℕ := (range m).filter
      (fun j : ℕ => ∃ x ∈ S, x ∈ Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m)) with hbad
    have hbad_card : bad.card ≤ S.card := by
      have hsub : bad ⊆ S.image (fun x : ℝ => ⌊(m : ℝ) * x⌋₊) := by
        intro j hj
        rw [hbad, Finset.mem_filter] at hj
        obtain ⟨_, x, hxS, hx⟩ := hj
        rw [Finset.mem_image]
        refine ⟨x, hxS, ?_⟩
        have h1 : (j : ℝ) < m * x := by
          have := hx.1; rw [div_lt_iff₀ hmpos] at this; linarith
        have h2 : m * x < (j : ℝ) + 1 := by
          have := hx.2; rw [lt_div_iff₀ hmpos] at this; linarith
        rw [Nat.floor_eq_iff (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])]
        exact ⟨h1.le, h2⟩
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    refine ⟨(range m) \ bad, ?_, ?_, ?_⟩
    · have h1 : (range m).card ≤ ((range m) \ bad).card + bad.card := by
        have := Finset.le_card_sdiff bad (range m)
        omega
      simp only [Finset.card_range] at h1
      omega
    · intro j hj
      exact Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
    · intro j hj
      rw [Finset.mem_sdiff] at hj
      obtain ⟨hjr, hjb⟩ := hj
      have hjm : j < m := Finset.mem_range.mp hjr
      have hns : ∀ x ∈ S, x ∉ Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m) := by
        intro x hxS hx
        exact hjb (by rw [hbad, Finset.mem_filter]; exact ⟨hjr, x, hxS, hx⟩)
      have hjle : ((j : ℝ) + 1) ≤ m := by exact_mod_cast hjm
      have hsub : Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m) ⊆ cellIcc 0 0 := by
        intro x hx
        rw [cellIcc_eq]
        unfold cL cR
        simp only [Int.cast_zero, pow_zero, zero_add, div_one]
        refine ⟨?_, ?_⟩
        · have := hx.1
          have h0 : (0 : ℝ) ≤ (j : ℝ) / m := by positivity
          linarith
        · have := hx.2
          have h1 : ((j : ℝ) + 1) / m ≤ 1 := by rw [div_le_one hmpos]; exact hjle
          linarith
      obtain ⟨α, β, h⟩ := affine_on_open T 0 0 _ _ hWF hsub hns
      exact ⟨α, β, h⟩

/-! ## Estimativa local numa célula de teste -/

/-- Piso `L¹` para afins numa célula `[c, c+t]` (versão geral de `L1_affine_interval`). -/
lemma L1_affine_cell {M : ℝ} (hM : 0 < M) (hbd : ∀ z, |deriv (deriv φB) z| ≤ M)
    {a : ℝ} (ha : 0 ≤ a) {c t : ℝ} (ht : 0 < t) (α β : ℝ) :
    t * (a * kappaB / M) ≤
      ∫ x in c..(c + t), |a * φB ((x - c) / t) - (α + β * x)| := by
  have hsub := L1_affine_lower hM hbd ha (α + β * c) (β * t)
  have hcomp := intervalIntegral.integral_comp_mul_add
    (f := fun x => |a * φB ((x - c) / t) - (α + β * x)|) (a := (0 : ℝ)) (b := 1)
    (c := t) ht.ne' c
  simp only [mul_zero, zero_add, mul_one] at hcomp
  rw [show t + c = c + t by ring] at hcomp
  have hint : ∫ y in (0 : ℝ)..1, |a * φB ((t * y + c - c) / t) -
      (α + β * (t * y + c))| = ∫ y in (0 : ℝ)..1, |a * φB y - ((α + β * c) + (β * t) * y)| := by
    apply intervalIntegral.integral_congr
    intro y _
    simp only
    have e1 : (t * y + c - c) / t = y := by field_simp; ring
    rw [e1]
    congr 2
    ring
  rw [hint] at hcomp
  have hI : a * kappaB / M ≤ ∫ y in (0 : ℝ)..1,
      |a * φB y - ((α + β * c) + (β * t) * y)| := by
    rw [div_le_iff₀ hM]; linarith [hsub]
  have h2 : ∫ x in c..(c + t), |a * φB ((x - c) / t) - (α + β * x)| =
      t * ∫ y in (0 : ℝ)..1, |a * φB y - ((α + β * c) + (β * t) * y)| := by
    rw [hcomp, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  rw [h2]
  exact mul_le_mul_of_nonneg_left hI ht.le

/-- `L^1 ⇒ L^p` num intervalo `[c, c+t]` (versão sem `c + t = 1` de `lp_lower_of_L1`). -/
lemma lp_lower_cell {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) {h : ℝ → ℝ} (hh : Continuous h)
    {c t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal ((∫ x in c..(c + t), |h x|) * t ^ (p.toReal⁻¹ - 1)) ≤
      eLpNorm h p (volume.restrict (Icc c (c + t))) := by
  set μ := volume.restrict (Icc c (c + t)) with hμ
  have hmu : μ Set.univ = ENNReal.ofReal t := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Icc]; congr 1; ring
  have hkey := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (f := h) (p := 1) (q := p)
    hp1 hh.aestronglyMeasurable
  have hp1r : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp1
    simpa using this
  have hinv : p.toReal⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1r
  have hexp : (1 : ℝ) / (1 : ℝ≥0∞).toReal - 1 / p.toReal = 1 - p.toReal⁻¹ := by
    simp [one_div]
  rw [hmu, hexp, ENNReal.ofReal_rpow_of_nonneg ht.le (by linarith),
    eLpNorm_one_interval hh (by linarith)] at hkey
  have hI : 0 ≤ ∫ x in c..(c + t), |h x| :=
    intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  have hX : ENNReal.ofReal (t ^ (1 - p.toReal⁻¹)) * ENNReal.ofReal (t ^ (p.toReal⁻¹ - 1)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht]
    norm_num
  calc ENNReal.ofReal ((∫ x in c..(c + t), |h x|) * t ^ (p.toReal⁻¹ - 1))
      = ENNReal.ofReal (∫ x in c..(c + t), |h x|) * ENNReal.ofReal (t ^ (p.toReal⁻¹ - 1)) :=
        ENNReal.ofReal_mul hI
    _ ≤ (eLpNorm h p μ * ENNReal.ofReal (t ^ (1 - p.toReal⁻¹))) *
          ENNReal.ofReal (t ^ (p.toReal⁻¹ - 1)) := mul_le_mul_of_nonneg_right hkey (zero_le _)
    _ = eLpNorm h p μ * (ENNReal.ofReal (t ^ (1 - p.toReal⁻¹)) *
          ENNReal.ofReal (t ^ (p.toReal⁻¹ - 1))) := by rw [mul_assoc]
    _ = eLpNorm h p μ := by rw [hX, mul_one]

/-- Na célula `(j/m, (j+1)/m)` só o bump `j` é não nulo. -/
lemma Fm_on_cell {m j : ℕ} (hj : j < m) (A : ℝ) {x : ℝ}
    (hx : x ∈ Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m)) :
    Fm m A x = A * φB (m * x - j) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have h1 : (j : ℝ) < m * x := by
    have := hx.1; rw [div_lt_iff₀ hmpos] at this; linarith
  have h2 : m * x < (j : ℝ) + 1 := by
    have := hx.2; rw [lt_div_iff₀ hmpos] at this; linarith
  unfold Fm
  congr 1
  refine Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj) (fun i _ hij => ?_)
  apply φB_eq_zero_of_not_mem
  intro hmem
  have hlo := hmem.1
  have hhi := hmem.2
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
    linarith
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hgt
    linarith


/-- Cota inferior local: numa célula de teste em que `g` é afim, o erro `L^p` da soma de bumps é
`≥ (A κ / M) · m^{-1/p}`. Vale para todo `p ≥ 1` (inclusive `p = 1`). -/
lemma cell_lower {p : ℝ} (hp : 1 ≤ p) {M : ℝ} (hM : 0 < M)
    (hbd : ∀ z, |deriv (deriv φB) z| ≤ M) {m j : ℕ} (hm : 1 ≤ m) (hj : j < m)
    {A : ℝ} (hA : 0 ≤ A) {g : ℝ → ℝ} {α β : ℝ}
    (hg : ∀ x ∈ Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m), g x = α + β * x) :
    ENNReal.ofReal (A * kappaB / M * (1 / (m : ℝ)) ^ p⁻¹) ≤
      eLpNorm (Fm m A - g) (ENNReal.ofReal p)
        (volume.restrict (Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m))) := by
  have hp0 : 0 < p := by linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set c : ℝ := (j : ℝ) / m with hc
  set t : ℝ := 1 / (m : ℝ) with ht_def
  have ht : 0 < t := by positivity
  have hct : ((j : ℝ) + 1) / m = c + t := by rw [hc, ht_def]; ring
  have harg : ∀ x : ℝ, (x - c) / t = m * x - j := by
    intro x; rw [hc, ht_def]; field_simp
  set h : ℝ → ℝ := fun x => A * φB ((x - c) / t) - (α + β * x) with hh_def
  have hhc : Continuous h := by
    rw [hh_def]
    exact (continuous_const.mul (φB_smooth.continuous.comp
      ((continuous_id.sub continuous_const).div_const t))).sub
      (continuous_const.add (continuous_const.mul continuous_id))
  have hμ : (Fm m A - g) =ᵐ[volume.restrict (Ioo c (c + t))] h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx' : x ∈ Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m) := by rw [hct]; exact hx
    simp only [Pi.sub_apply, hh_def]
    rw [Fm_on_cell hj A hx', hg x hx', harg]
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hPt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hLp := lp_lower_cell hP1 hPt hhc ht (c := c)
  rw [ENNReal.toReal_ofReal hp0.le] at hLp
  have hL1 := L1_affine_cell hM hbd hA ht (c := c) α β
  have hset : (volume.restrict (Ioo c (c + t))) = volume.restrict (Icc c (c + t)) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  rw [hct, hset]
  have heq : eLpNorm (Fm m A - g) (ENNReal.ofReal p) (volume.restrict (Icc c (c + t))) =
      eLpNorm h (ENNReal.ofReal p) (volume.restrict (Icc c (c + t))) := by
    rw [← hset]; exact eLpNorm_congr_ae hμ
  rw [heq]
  have hexp : t ^ p⁻¹ = t * t ^ (p⁻¹ - 1) := by
    have := Real.rpow_add ht 1 (p⁻¹ - 1)
    rw [Real.rpow_one, show (1 : ℝ) + (p⁻¹ - 1) = p⁻¹ by ring] at this
    exact this
  calc ENNReal.ofReal (A * kappaB / M * t ^ p⁻¹)
      = ENNReal.ofReal ((t * (A * kappaB / M)) * t ^ (p⁻¹ - 1)) := by
        congr 1; rw [hexp]; ring
    _ ≤ ENNReal.ofReal ((∫ x in c..(c + t), |h x|) * t ^ (p⁻¹ - 1)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hL1 (Real.rpow_nonneg ht.le _))
    _ ≤ _ := hLp


/-! ## Agregação em `L^p([0,1])` -/

lemma eLpNorm_rpow_eq {p : ℝ} (hp : 1 ≤ p) (F : ℝ → ℝ) (μ : Measure ℝ) :
    eLpNorm F (ENNReal.ofReal p) μ ^ p = ∫⁻ x, ‖F x‖ₑ ^ p ∂μ := by
  have hp0 : 0 < p := by linarith
  have hne0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne',
    ENNReal.rpow_one]

lemma cells_disjoint {m : ℕ} (hm : 1 ≤ m) (G : Finset ℕ) :
    Set.PairwiseDisjoint (↑G : Set ℕ)
      (fun j : ℕ => Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  intro i _ j _ hij
  rw [Function.onFun, Set.disjoint_left]
  intro x hxi hxj
  have h1 : (i : ℝ) < m * x := by
    have := hxi.1; rw [div_lt_iff₀ hmpos] at this; linarith
  have h2 : m * x < (i : ℝ) + 1 := by
    have := hxi.2; rw [lt_div_iff₀ hmpos] at this; linarith
  have h3 : (j : ℝ) < m * x := by
    have := hxj.1; rw [div_lt_iff₀ hmpos] at this; linarith
  have h4 : m * x < (j : ℝ) + 1 := by
    have := hxj.2; rw [lt_div_iff₀ hmpos] at this; linarith
  have a1 : (i : ℝ) < j + 1 := by linarith
  have a2 : (j : ℝ) < i + 1 := by linarith
  have a1' : i < j + 1 := by exact_mod_cast a1
  have a2' : j < i + 1 := by exact_mod_cast a2
  exact hij (by omega)

/-- Se `‖F‖_{L^p(cell_j)} ≥ c0` em `|G|` células disjuntas, então
`c0^p · |G| ≤ ‖F‖_{L^p([0,1])}^p`. -/
lemma agg_lower {p : ℝ} (hp : 1 ≤ p) {m : ℕ} (hm : 1 ≤ m) {F : ℝ → ℝ} (G : Finset ℕ)
    (hG : ∀ j ∈ G, j < m) {c0 : ℝ≥0∞}
    (h : ∀ j ∈ G, c0 ≤ eLpNorm F (ENNReal.ofReal p)
      (volume.restrict (Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m)))) :
    c0 ^ p * (G.card : ℝ≥0∞) ≤ eLpNorm F (ENNReal.ofReal p) vol01 ^ p := by
  have hp0 : 0 < p := by linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hcell : ∀ j ∈ G, c0 ^ p ≤ ∫⁻ x in Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m), ‖F x‖ₑ ^ p := by
    intro j hj
    rw [← eLpNorm_rpow_eq hp]
    exact ENNReal.rpow_le_rpow (h j hj) hp0.le
  have hsum : (G.card : ℝ≥0∞) * c0 ^ p ≤
      ∑ j ∈ G, ∫⁻ x in Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m), ‖F x‖ₑ ^ p := by
    calc (G.card : ℝ≥0∞) * c0 ^ p = ∑ _j ∈ G, c0 ^ p := by simp
      _ ≤ _ := Finset.sum_le_sum hcell
  have hU : ∑ j ∈ G, ∫⁻ x in Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m), ‖F x‖ₑ ^ p
      = ∫⁻ x in ⋃ j ∈ G, Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m), ‖F x‖ₑ ^ p :=
    (lintegral_biUnion_finset (cells_disjoint hm G) (fun j _ => measurableSet_Ioo) _).symm
  have hsub : (⋃ j ∈ G, Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m)) ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, hj, hxj⟩ := hx
    have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast hG j hj
    refine ⟨?_, ?_⟩
    · have h0 : (0 : ℝ) ≤ (j : ℝ) / m := by positivity
      linarith [hxj.1]
    · have h1 : ((j : ℝ) + 1) / m ≤ 1 := by rw [div_le_one hmpos]; exact hjm
      linarith [hxj.2]
  have hfin : (∫⁻ x in ⋃ j ∈ G, Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m), ‖F x‖ₑ ^ p)
      ≤ ∫⁻ x in Icc (0 : ℝ) 1, ‖F x‖ₑ ^ p := lintegral_mono_set hsub
  have hvol : eLpNorm F (ENNReal.ofReal p) vol01 ^ p = ∫⁻ x in Icc (0 : ℝ) 1, ‖F x‖ₑ ^ p :=
    eLpNorm_rpow_eq hp F vol01
  rw [hvol, mul_comm]
  exact hsum.trans (hU ▸ hfin)


/-! ## Cota inferior por distância e passagem ao minimax -/

/-- Para `g ∈ Σ_{N,H}`: `‖Fm(2N) A - g‖_{L^p} ≥ A κ / (2M)`. Vale para todo `p ≥ 1`. -/
lemma leaf_dist_lower {p : ℝ} (hp : 1 ≤ p) {M : ℝ} (hM : 0 < M)
    (hbd : ∀ z, |deriv (deriv φB) z| ≤ M) {N H : ℕ} (hN : 1 ≤ N)
    {A : ℝ} (hA : 0 ≤ A) {g : ℝ → ℝ} (hg : g ∈ Pendencias.Agenda.Sigma (fun _ => H) N) :
    ENNReal.ofReal (A * kappaB / (2 * M)) ≤
      distP (ENNReal.ofReal p) (Fm (2 * N) A) g := by
  have hp0 : 0 < p := by linarith
  have hκ : 0 < kappaB := kappaB_pos
  obtain ⟨G, hGcard, hGlt, hGaff⟩ := exists_good_cells (g := g) (H := H) hN hg
  set m : ℕ := 2 * N with hm
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set B : ℝ := A * kappaB / M with hB
  have hB0 : 0 ≤ B := by positivity
  set cl : ℝ := B * (1 / (m : ℝ)) ^ p⁻¹ with hcl
  have hcl0 : 0 ≤ cl := by positivity
  have hcells : ∀ j ∈ G, ENNReal.ofReal cl ≤ eLpNorm (Fm m A - g) (ENNReal.ofReal p)
      (volume.restrict (Ioo ((j : ℝ) / m) (((j : ℝ) + 1) / m))) := by
    intro j hj
    obtain ⟨α, β, hab⟩ := hGaff j hj
    exact cell_lower hp hM hbd hm1 (hGlt j hj) hA hab
  have hagg := agg_lower hp hm1 (F := Fm m A - g) G hGlt hcells
  -- álgebra real
  have hcl_p : cl ^ p = B ^ p * (1 / (m : ℝ)) := by
    rw [hcl, Real.mul_rpow hB0 (by positivity), ← Real.rpow_mul (by positivity),
      inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have h2p : (2 : ℝ) ≤ (2 : ℝ) ^ p := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ (2 : ℝ) ^ p := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp
  have hhalf : (A * kappaB / (2 * M)) ^ p ≤ B ^ p / 2 := by
    have e : A * kappaB / (2 * M) = B / 2 := by rw [hB]; field_simp
    rw [e, Real.div_rpow hB0 (by norm_num)]
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) h2p
  have hlow : ENNReal.ofReal (A * kappaB / (2 * M)) ^ p ≤
      eLpNorm (Fm m A - g) (ENNReal.ofReal p) vol01 ^ p := by
    calc ENNReal.ofReal (A * kappaB / (2 * M)) ^ p
        = ENNReal.ofReal ((A * kappaB / (2 * M)) ^ p) :=
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le
      _ ≤ ENNReal.ofReal (B ^ p / 2) := ENNReal.ofReal_le_ofReal hhalf
      _ = ENNReal.ofReal (cl ^ p) * (N : ℝ≥0∞) := by
          rw [hcl_p, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hm]; push_cast; field_simp
      _ ≤ ENNReal.ofReal cl ^ p * (G.card : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_rpow_of_nonneg hcl0 hp0.le]
          gcongr
      _ ≤ _ := hagg
  have := (ENNReal.rpow_le_rpow_iff hp0).mp hlow
  unfold distP
  exact this

/-- **Piso pelo número de folhas** (`lp:lem:leaf-budget-floor`): existe `c_leaf = c(p,s,q) > 0`
tal que `D_{p,s,q}(N,H) ≥ c_leaf N^{-s}` para todos `N, H ≥ 2`. -/
theorem leaf_floor_const {p s : ℝ} {q : ℝ≥0∞} (hp : 1 ≤ p) (hs0 : 0 < s) (hs2 : s < 2)
    (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ N H : ℕ, 2 ≤ N → 2 ≤ H →
      ENNReal.ofReal (c * (N : ℝ) ^ (-s)) ≤ FormalizacaoMinimax.Dfun p s q N H := by
  obtain ⟨b, hb0, hb⟩ := packing_norm_le hp hs0 hs2 hq
  obtain ⟨M, hM0, hM⟩ := exists_M_φB
  have hκ : 0 < kappaB := kappaB_pos
  refine ⟨b * (2 : ℝ) ^ (-s) * kappaB / (2 * M), by positivity, ?_⟩
  intro N H hN hH
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set m : ℕ := 2 * N with hm
  have hm1 : 1 ≤ m := by omega
  set A : ℝ := b * (m : ℝ) ^ (-s) with hA
  have hA0 : 0 ≤ A := by positivity
  have hAeq : A = b * (2 : ℝ) ^ (-s) * (N : ℝ) ^ (-s) := by
    rw [hA, hm]; push_cast
    rw [Real.mul_rpow (by norm_num) hNpos.le]; ring
  refine FormalizacaoMinimax.le_Dfun (f := Fm m A) (measurable_Fm m A) (hb m hm1) ?_
  refine FormalizacaoMinimax.le_bestError_of_forall (fun g hg => ?_)
  have h := leaf_dist_lower hp hM0 hM hN1 hA0 hg
  have e : b * (2 : ℝ) ^ (-s) * kappaB / (2 * M) * (N : ℝ) ^ (-s) = A * kappaB / (2 * M) := by
    rw [hAeq]; ring
  rw [e]
  exact h


/-! ## Transferência dos pisos de altura (já existentes) ao funcional `Dfun`

Pequenos lemas de ponte: cada piso de altura de `AlturaFloor`, `AlturaSlope` e
`ArithmeticFloor` (enunciado como `∃ f` na bola, para todo `g ∈ Σ`) vale para `Dfun`. -/

/-- Piso geométrico `c H^{-s}` para `Dfun` (todo `0<s<2`, `0<q≤∞`, `p≥1`). -/
theorem dfun_geometric_floor {p s : ℝ} {q : ℝ≥0∞} (hp : 1 ≤ p) (hs0 : 0 < s) (hs2 : s < 2)
    (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ N H : ℕ, 2 ≤ N → 2 ≤ H →
      ENNReal.ofReal (c * (H : ℝ) ^ (-s)) ≤ FormalizacaoMinimax.Dfun p s q N H := by
  obtain ⟨c, hc, hfl⟩ := geometric_floor (p := ENNReal.ofReal p) (q := q) (s := s)
    (ENNReal.one_le_ofReal.mpr hp) ENNReal.ofReal_ne_top hq hs0 hs2
  refine ⟨c, hc, fun N H _ hH => ?_⟩
  obtain ⟨f, hfm, hball, hdist⟩ := hfl H hH
  exact FormalizacaoMinimax.le_Dfun hfm hball
    (FormalizacaoMinimax.le_bestError_of_forall (fun g hg => hdist N g hg))

/-- Piso por inclinação `c H^{-s/(1+1/p-s)}` para `Dfun`, `0 < s ≤ 1/p`. -/
theorem dfun_slope_floor {p s : ℝ} {q : ℝ≥0∞} (hp : 1 ≤ p) (hs0 : 0 < s) (hs2 : s < 2)
    (hsp : s ≤ 1 / p) (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ N H : ℕ, 2 ≤ N → 2 ≤ H →
      ENNReal.ofReal (c * (H : ℝ) ^ (-(s / (1 + (1 / p - s))))) ≤
        FormalizacaoMinimax.Dfun p s q N H := by
  have hp0 : 0 < p := by linarith
  have hsp' : s ≤ (ENNReal.ofReal p).toReal⁻¹ := by
    rw [ENNReal.toReal_ofReal hp0.le, ← one_div]; exact hsp
  obtain ⟨c, hc, hfl⟩ := slope_floor (p := ENNReal.ofReal p) (q := q) (s := s)
    (ENNReal.one_le_ofReal.mpr hp) ENNReal.ofReal_ne_top hq hs0 hs2 hsp'
  refine ⟨c, hc, fun N H _ hH => ?_⟩
  obtain ⟨f, hfm, hball, hdist⟩ := hfl H hH
  have key := FormalizacaoMinimax.le_Dfun hfm hball
    (FormalizacaoMinimax.le_bestError_of_forall (fun g hg => hdist N g hg))
  rw [ENNReal.toReal_ofReal hp0.le] at key
  simpa only [one_div] using key

/-- Piso aritmético `1/(2H)` para `Dfun` (todo `p ≥ 1`, `0<s`, `0<q≤∞`). -/
theorem dfun_arithmetic_floor {p s : ℝ} {q : ℝ≥0∞} (hp : 1 ≤ p) (hs0 : 0 < s) (hq : 0 < q)
    {N H : ℕ} (_hN : 1 ≤ N) (hH : 2 ≤ H) :
    ENNReal.ofReal (1 / (2 * (H : ℝ))) ≤ FormalizacaoMinimax.Dfun p s q N H := by
  have hHpos : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
  have hval : FormalizacaoFloor.floorValue H ≤ 1 := by
    unfold FormalizacaoFloor.floorValue
    rw [div_le_one (by positivity)]; linarith
  have hval0 : 0 ≤ FormalizacaoFloor.floorValue H := by
    unfold FormalizacaoFloor.floorValue; positivity
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  refine FormalizacaoMinimax.le_Dfun (f := fun _ => FormalizacaoFloor.floorValue H)
    measurable_const (besovNorm_const_le hP1 ENNReal.ofReal_ne_top hq hs0 hval0 hval) ?_
  refine FormalizacaoMinimax.le_bestError_of_forall (fun g hg => ?_)
  have := FormalizacaoFloor.arithmetic_floor_lp hP1 (N := N) (H := H) (by omega) hg
  simpa [FormalizacaoFloor.floorValue] using this


end FormalizacaoLeaf
