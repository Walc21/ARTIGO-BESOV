import Formalizacao.MinimaxDefs

open scoped ENNReal
open MeasureTheory Set Filter Artigo FormalizacaoLp FormalizacaoLow FormalizacaoFloor
open FormalizacaoMinimax

namespace F6
private theorem volumeUnit : vol01 univ = 1 := by simp [vol01, Real.volume_Icc]

-- Translate equalities only where the original interval contains the shifted point.
private theorem shift_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[vol01] g) {h c : ℝ}
    (hc : 0 ≤ c) (hc' : c ≤ 2 * h) :
    (fun x => f (x + c)) =ᵐ[volume.restrict (Icc 0 (1 - 2 * h))]
      (fun x => g (x + c)) := by
  have hglobal := (ae_restrict_iff' measurableSet_Icc).mp hfg
  have hshift :=
    (measurePreserving_add_right (volume : Measure ℝ) c).quasiMeasurePreserving.ae hglobal
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hshift] with x hx hxI
  exact hx ⟨by linarith [hxI.1], by linarith [hxI.2]⟩

theorem wtP_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[vol01] g) (p : ℝ≥0∞) (t : ℝ) :
    wtP p t f = wtP p t g := by
  unfold wtP
  congr 1
  funext h
  congr 1
  funext hh
  have h0 : 0 ≤ h := hh.1.le
  apply eLpNorm_congr_ae
  filter_upwards [shift_ae hfg (c := 0) le_rfl (by linarith),
    shift_ae hfg (c := h) h0 (by linarith),
    shift_ae hfg (c := 2 * h) (by positivity) le_rfl] with x hx0 hx1 hx2
  simp only [add_zero] at hx0
  simp only [diff2, hx0, hx1, hx2]

theorem ball_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[vol01] g) (p : ℝ≥0∞) (s : ℝ)
    (q : ℝ≥0∞) : besovNorm p s q f = besovNorm p s q g := by
  have hseq : FormalizacaoRed.besovSeq p s f = FormalizacaoRed.besovSeq p s g := by
    funext r
    simp only [FormalizacaoRed.besovSeq, wtP_congr_ae hfg]
  simp only [besovNorm, hseq, eLpNorm_congr_ae hfg]

theorem bestError_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[vol01] g) (p : ℝ≥0∞) (N H : ℕ) :
    bestError p N H f = bestError p N H g := by
  have hdist (u : ℝ → ℝ) : distP p f u = distP p g u :=
    eLpNorm_congr_ae (hfg.sub (EventuallyEq.rfl : u =ᵐ[vol01] u))
  simp only [bestError, hdist]

-- Every a.e.-measurable target has a globally measurable representative with the same data.
example (f : ℝ → ℝ) (hf : AEMeasurable f vol01) (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞)
    (N H : ℕ) :
    ∃ g : ℝ → ℝ, Measurable g ∧ besovNorm p s q f = besovNorm p s q g ∧
      bestError p N H f = bestError p N H g :=
  ⟨hf.mk f, hf.measurable_mk, ball_congr_ae hf.ae_eq_mk p s q,
    bestError_congr_ae hf.ae_eq_mk p N H⟩

-- Changing the domain of representatives to the completed measure preserves the supremum.
theorem Dfun_eq_sup_aemeasurable (p s : ℝ) (q : ℝ≥0∞) (N H : ℕ) :
    Dfun p s q N H =
      ⨆ (f : ℝ → ℝ) (_ : AEMeasurable f vol01)
        (_ : besovNorm (ENNReal.ofReal p) s q f ≤ 1), bestError (ENNReal.ofReal p) N H f := by
  unfold Dfun
  apply le_antisymm
  · refine iSup_le fun f => iSup_le fun hf => iSup_le fun hb => ?_
    exact le_iSup_of_le f (le_iSup_of_le hf.aemeasurable
      (le_iSup (fun _ : besovNorm (ENNReal.ofReal p) s q f ≤ 1 =>
        bestError (ENNReal.ofReal p) N H f) hb))
  · refine iSup_le fun f => iSup_le fun hf => iSup_le fun hb => ?_
    let g := hf.mk f
    have hbg : besovNorm (ENNReal.ofReal p) s q g ≤ 1 :=
      (ball_congr_ae hf.ae_eq_mk (ENNReal.ofReal p) s q).symm.trans_le hb
    rw [bestError_congr_ae hf.ae_eq_mk]
    exact le_iSup_of_le g (le_iSup_of_le hf.measurable_mk
      (le_iSup (fun _ : besovNorm (ENNReal.ofReal p) s q g ≤ 1 =>
        bestError (ENNReal.ofReal p) N H g) hbg))

-- Nonemptiness at minimal budgets and the additional zero candidate.
private def rootAtom : Atom := ⟨0, 0, 0, 1, by decide⟩

example : (classNH 2 2).Nonempty := by
  refine ⟨(LTree.leaf rootAtom).eval 0 0, LTree.leaf rootAtom, ?_, rfl⟩
  refine ⟨⟨rfl, rfl⟩, by decide +kernel, by decide +kernel⟩

example (N H : ℕ) :
    Pendencias.Agenda.Sigma (fun _ ↦ H) N = {0} ∪ classNH N H := rfl

-- Shared endpoint disagreement is rejected by WF.
private def leftAtom : Atom := ⟨1, 0, 0, 1, by decide⟩
private def rightAtom : Atom := ⟨1, 1, 0, 1, by decide⟩

example : ¬ AdmNH 2 2 (LTree.node (LTree.leaf leftAtom) (LTree.leaf rightAtom)) := by
  norm_num [AdmNH, LTree.WF, LTree.rval, LTree.lval, leftAtom, rightAtom,
    Atom.lval_eq, Atom.rval_eq]

-- Degenerate height excludes a concrete admissible root leaf. Rational height is reduced.
example : ¬ AdmNH 2 1 (LTree.leaf rootAtom) := by
  intro h
  have ha : rootAtom.height ≤ 1 := (LTree.le_maxHeight (by simp [LTree.leaves])).trans h.2.2
  exact (by decide +kernel : ¬ rootAtom.height ≤ 1) ha

example : ht ((6 : ℚ) / 8) = 4 := by decide +kernel
example : ht ((-6 : ℚ) / 8) = 4 := by decide +kernel

-- Constant targets distinguish Lp error from a homogeneous seminorm, even at the exact radius.
theorem norm_const {p q : ℝ≥0∞} (hp : p ≠ 0) (hq : 0 < q) (s a : ℝ) :
    besovNorm p s q (fun _ ↦ a) = ENNReal.ofReal |a| := by
  have hz (t : ℝ) : wtP p t (fun _ ↦ a) = 0 := by
    have hh (h : ℝ) : diff2 h (fun _ ↦ a) = 0 := by funext x; simp [diff2]; ring
    simp [wtP, hh]
  have hs : FormalizacaoRed.besovSeq p s (fun _ ↦ a) = 0 := by
    funext k; simp [FormalizacaoRed.besovSeq, hz]
  have hμ : vol01 ≠ 0 := by
    intro hempty
    have h := volumeUnit
    simp [hempty] at h
  have hzq : lqNorm q (0 : ℕ → ℝ≥0∞) = 0 := FormalizacaoLq.lqNorm_zero hq
  rw [besovNorm, hs, hzq, add_zero, eLpNorm_const a hp hμ]
  simp [← ofReal_norm_eq_enorm, Real.norm_eq_abs]

example : besovNorm 1 1 ⊤ (fun _ ↦ 1) ≤ 1 := by
  rw [norm_const one_ne_zero ENNReal.zero_lt_top]
  norm_num

example : ¬ besovNorm 1 1 ⊤ (fun _ ↦ 2) ≤ 1 := by
  rw [norm_const one_ne_zero ENNReal.zero_lt_top]
  norm_num

-- The arithmetic-floor witness also attains the upper bound by choosing zero.
example (N : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    bestError 1 N H (fun _ ↦ floorValue H) = ENNReal.ofReal (floorValue H) := by
  apply le_antisymm _ (arithmetic_floor_bestError le_rfl N hH)
  have hz : (0 : ℝ → ℝ) ∈ Pendencias.Agenda.Sigma (fun _ ↦ H) N := Or.inl rfl
  refine (iInf₂_le (f := fun g _ => distP 1 (fun _ ↦ floorValue H) g) 0 hz).trans ?_
  rw [distP, sub_zero, eLpNorm_one_eq_lintegral_enorm]
  have hnonneg : 0 ≤ floorValue H := by unfold floorValue; positivity
  simp [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg hnonneg]

#print axioms wtP_congr_ae
#print axioms ball_congr_ae
#print axioms bestError_congr_ae
#print axioms norm_const
#print axioms Dfun_eq_sup_aemeasurable

end F6
