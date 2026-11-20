import Formalizacao.UnifTheorem
import RequestProject.Codecs

/-!
# Descrições binárias com altura fixa (seção 6.2)

O orçamento `H` é compartilhado. Depois de um bit para o caso zero, vêm a forma
da árvore em pré-ordem e os pares racionais das folhas em ordem espacial.
-/

open Artigo Set

namespace FormalizacaoBits

/-- Número de bits de cada magnitude de uma coordenada racional. -/
def coordinateWidth (H : ℕ) : ℕ := Nat.clog 2 (H + 1)

lemma coordinateWidth_eq (H : ℕ) :
    coordinateWidth H = ⌈Real.logb 2 ((H : ℝ) + 1)⌉₊ := by
  simpa [coordinateWidth] using (Real.natCeil_logb_natCast 2 (H + 1)).symm

/-- Codec de largura fixa, com sinal, magnitude do numerador e denominador. -/
def fixedRat (w : ℕ) : Codec ℚ where
  enc y := decide (y.num < 0) :: (toBits w y.num.natAbs ++ toBits w y.den)
  dec bs := match bs with
    | [] => none
    | b :: tail =>
      let n : ℤ := ofBits (tail.take w)
      let d : ℤ := ofBits ((tail.drop w).take w)
      some (Rat.divInt (if b then -n else n) d, tail.drop (2 * w))

@[simp] lemma fixedRat_length (w : ℕ) (y : ℚ) :
    ((fixedRat w).enc y).length = 2 * w + 1 := by simp [fixedRat, two_mul]

private lemma fixedRat_rt (H : ℕ) : (fixedRat (coordinateWidth H)).RT (fun y ↦ ht y ≤ H) := by
  intro y hy t
  let w := coordinateWidth H
  have hH : H < 2 ^ w := Nat.lt_of_succ_le (Nat.le_pow_clog (by norm_num) _)
  have hn : y.num.natAbs < 2 ^ w := ((le_max_left _ _).trans hy).trans_lt hH
  have hd : y.den < 2 ^ w := ((le_max_right _ _).trans hy).trans_lt hH
  have hs : (if y.num < 0 then -((y.num.natAbs : ℕ) : ℤ) else (y.num.natAbs : ℤ)) = y.num := by
    split_ifs with h
    · exact Int.ofNat_natAbs_of_nonpos h.le ▸ neg_neg y.num
    · exact Int.natAbs_of_nonneg (le_of_not_gt h)
  change (fixedRat w).dec ((fixedRat w).enc y ++ t) = some (y, t)
  simp only [fixedRat, List.cons_append, List.append_assoc, decide_eq_true_eq]
  rw [List.take_left' (by simp), List.drop_left' (by simp), List.take_left' (by simp),
    ofBits_toBits _ _ hn, ofBits_toBits _ _ hd, hs, Rat.num_divInt_den]
  congr 1
  rw [two_mul, ← List.drop_drop, List.drop_left' (by simp), List.drop_left' (by simp)]

/-- Forma em pré-ordem. `false` é folha e `true` é nó interno. -/
def shapeWord : LTree → List Bool
  | .leaf _ => [false]
  | .node l r => true :: (shapeWord l ++ shapeWord r)

private lemma shape_length (T : LTree) : (shapeWord T).length + 1 = 2 * T.numLeaves := by
  induction T with
  | leaf a => rfl
  | node l r hl hr =>
    simp only [shapeWord, List.length_cons, List.length_append, LTree.numLeaves_node]
    omega

private lemma shape_parse (T U : LTree) (s t : List Bool)
    (h : shapeWord T ++ s = shapeWord U ++ t) : shapeWord T = shapeWord U ∧ s = t := by
  induction T generalizing U s t with
  | leaf a =>
    cases U with
    | leaf b => exact ⟨rfl, by simpa [shapeWord] using h⟩
    | node l r => simp [shapeWord] at h
  | node l r hl hr =>
    cases U with
    | leaf b => simp [shapeWord] at h
    | node u v =>
      have h' : shapeWord l ++ (shapeWord r ++ s) = shapeWord u ++ (shapeWord v ++ t) := by
        simpa only [shapeWord, List.cons_append, List.cons.injEq, true_and, List.append_assoc] using h
      obtain ⟨hlu, hs⟩ := hl u _ _ h'
      obtain ⟨hrv, hst⟩ := hr v _ _ hs
      exact ⟨by simp only [shapeWord, hlu, hrv], hst⟩

private def coordinates (T : LTree) : List (ℚ × ℚ) :=
  T.leaves.map fun a ↦ (a.y0, a.s)

private lemma coordinates_length (T : LTree) : (coordinates T).length = T.numLeaves :=
  List.length_map _ |>.trans rfl

private lemma tree_eq_of_shape_coordinates (T U : LTree) {k : ℕ} {m : ℤ}
    (hT : T.WF k m) (hU : U.WF k m) (hs : shapeWord T = shapeWord U)
    (hc : coordinates T = coordinates U) : T = U := by
  induction T generalizing U k m with
  | leaf a =>
    cases U with
    | leaf b =>
      have hc' : a.y0 = b.y0 ∧ a.s = b.s := by simpa [coordinates, LTree.leaves] using hc
      have hk : a.k = b.k := hT.1.trans hU.1.symm
      have hm : a.m = b.m := hT.2.trans hU.2.symm
      cases a
      cases b
      simp_all
    | node l r => simp [shapeWord] at hs
  | node l r hl hr =>
    cases U with
    | leaf b => simp [shapeWord] at hs
    | node u v =>
      have hs' : shapeWord l ++ shapeWord r = shapeWord u ++ shapeWord v := by
        simpa [shapeWord] using hs
      obtain ⟨hlu, hrv⟩ := shape_parse l u _ _ hs'
      have hlen : (coordinates l).length = (coordinates u).length := by
        have h := congrArg List.length hlu
        have := shape_length l
        have := shape_length u
        simp only [coordinates_length]
        omega
      have hc' : coordinates l ++ coordinates r = coordinates u ++ coordinates v := by
        simpa [coordinates, LTree.leaves] using hc
      obtain ⟨hcl, hcr⟩ := List.append_inj hc' hlen
      rw [hl u hT.1 hU.1 hlu hcl, hr v hT.2.1 hU.2.1 hrv hcr]

private def coordinateCodec (H : ℕ) : Codec (ℚ × ℚ) :=
  (fixedRat (coordinateWidth H)).prod (fixedRat (coordinateWidth H))

private lemma coordinateCodec_rt (H : ℕ) :
    (coordinateCodec H).RT (fun y ↦ ht y.1 ≤ H ∧ ht y.2 ≤ H) :=
  (fixedRat_rt H).prod (fixedRat_rt H)

private lemma coordinates_height {T : LTree} {H : ℕ} (hh : T.maxHeight ≤ H) :
    ∀ y ∈ coordinates T, ht y.1 ≤ H ∧ ht y.2 ≤ H := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  have h := LTree.maxHeight_le_iff.mp hh a ha
  exact ⟨a.ht_y0_le_height.trans h, a.ht_s_le_height.trans h⟩

/-- Descrição de uma representação, rotulada com `true` para distingui-la do código zero. -/
def treeWord (H : ℕ) (T : LTree) : List Bool :=
  true :: (shapeWord T ++ (coordinateCodec H).encList (coordinates T))

lemma treeWord_length (H : ℕ) (T : LTree) :
    (treeWord H T).length = 4 * T.numLeaves * (coordinateWidth H + 1) := by
  have h := shape_length T
  rw [treeWord, List.length_cons, List.length_append, Codec.encList_length]
  have he (y : ℚ × ℚ) : ((coordinateCodec H).enc y).length = 4 * coordinateWidth H + 2 := by
    simp [coordinateCodec, Codec.prod]
    omega
  simp only [he, List.map_const', List.sum_replicate, coordinates_length, smul_eq_mul]
  nlinarith

/-- As descrições de árvores admissíveis são livres de prefixo e determinam a árvore. -/
theorem treeWord_prefix {H : ℕ} {T U : LTree} (hT : T.WF 0 0) (hU : U.WF 0 0)
    (hTH : T.maxHeight ≤ H) (hUH : U.maxHeight ≤ H) (hp : treeWord H T <+: treeWord H U) :
    T = U := by
  obtain ⟨t, ht⟩ := hp
  change treeWord H T ++ t = treeWord H U at ht
  have hs' : shapeWord T ++ ((coordinateCodec H).encList (coordinates T) ++ t) =
      shapeWord U ++ (coordinateCodec H).encList (coordinates U) := by
    simpa only [treeWord, List.cons_append, List.append_assoc, List.cons.injEq, true_and] using ht
  obtain ⟨hs, hc⟩ := shape_parse T U _ _ hs'
  have hl : (coordinates T).length = (coordinates U).length := by
    simp only [coordinates_length]
    have h := congrArg List.length hs
    have := shape_length T
    have := shape_length U
    omega
  have h₁ := (coordinateCodec_rt H).decN _ (coordinates_height hTH) t
  have h₂ := (coordinateCodec_rt H).decN _ (coordinates_height hUH) []
  rw [hl, hc, ← List.append_nil ((coordinateCodec H).encList (coordinates U)), h₂] at h₁
  exact tree_eq_of_shape_coordinates T U hT hU hs (congrArg Prod.fst (Option.some.inj h₁)).symm

/-- Biblioteca apontada com altura fixa. -/
abbrev boundedLibrary (N H : ℕ) : Set (ℝ → ℝ) := Pendencias.Agenda.Sigma (fun _ ↦ H) N

/-- Um código para cada função, escolhendo uma representação admissível para as não nulas. -/
noncomputable def libraryWord {N H : ℕ} (g : boundedLibrary N H) : List Bool := by
  classical
  exact if hz : g.val = 0 then [false] else
    treeWord H (g.property.resolve_left hz).choose

/-- Proposição sobre bits: comprimento e ausência de prefixos próprios na biblioteca apontada. -/
theorem boundedLibrary_code (N H : ℕ) (hN : 1 ≤ N) :
    (∀ g : boundedLibrary N H, (libraryWord g).length ≤ 4 * N * (coordinateWidth H + 1)) ∧
      ∀ g g' : boundedLibrary N H, libraryWord g <+: libraryWord g' → g = g' := by
  classical
  constructor
  · intro g
    by_cases hz : g.val = 0
    · rw [libraryWord, dif_pos hz]
      simp only [List.length_singleton]
      nlinarith
    · let T := (g.property.resolve_left hz).choose
      have hT := (g.property.resolve_left hz).choose_spec.1
      rw [libraryWord, dif_neg hz, treeWord_length]
      gcongr
      exact hT.2.1
  · intro g g' hp
    by_cases hz : g.val = 0 <;> by_cases hz' : g'.val = 0
    · exact Subtype.ext (hz.trans hz'.symm)
    · rw [libraryWord, dif_pos hz, libraryWord, dif_neg hz'] at hp
      obtain ⟨t, ht⟩ := hp
      simp [treeWord] at ht
    · rw [libraryWord, dif_neg hz, libraryWord, dif_pos hz'] at hp
      obtain ⟨t, ht⟩ := hp
      simp [treeWord] at ht
    · rw [libraryWord, dif_neg hz, libraryWord, dif_neg hz'] at hp
      obtain ⟨⟨hw, _, hh⟩, he⟩ := (g.property.resolve_left hz).choose_spec
      obtain ⟨⟨hw', _, hh'⟩, he'⟩ := (g'.property.resolve_left hz').choose_spec
      exact Subtype.ext (he.trans ((congrArg (fun T : LTree ↦ T.eval 0 0)
        (treeWord_prefix hw hw' hh hh' hp)).trans he'.symm))

/-- A cota cardinal é uma potência de dois de expoente igual ao máximo comprimento. -/
theorem boundedLibrary_card {N H : ℕ} (hN : 1 ≤ N) :
    Nat.card (boundedLibrary N H) ≤ 2 ^ (4 * N * (coordinateWidth H + 1)) := by
  classical
  letI : Fintype (boundedLibrary N H) := (Pendencias.Agenda.Sigma_finite _ _).fintype
  let W := Finset.univ.image (libraryWord (N := N) (H := H))
  have hcode := boundedLibrary_code N H hN
  have hinj : Function.Injective (libraryWord (N := N) (H := H)) :=
    fun g g' he ↦ hcode.2 g g' (he ▸ List.prefix_refl _)
  have hcard : W.card = Nat.card (boundedLibrary N H) := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]
  rw [← hcard]
  apply Artigo.card_le_of_prefixFree W _
  · intro u hu v hv hp
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨g', _, rfl⟩ := Finset.mem_image.mp hv
    rw [hcode.2 g g' hp]
  · intro u hu
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hu
    exact hcode.1 g


/-- A cota sobre o logaritmo da cardinalidade, na forma inteira mais forte. -/
theorem boundedLibrary_log_card {N H : ℕ} (hN : 1 ≤ N) :
    Nat.clog 2 (Nat.card (boundedLibrary N H)) ≤ 4 * N * (coordinateWidth H + 1) :=
  Nat.clog_le_of_le_pow (boundedLibrary_card hN)

open scoped ENNReal
open FormalizacaoLow FormalizacaoLp MeasureTheory

private lemma Lfun_le_nat {N : ℕ} (hN : 1 ≤ N) : Lfun N ≤ N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Lfun, Real.log_mul (Real.exp_pos _).ne' hn.ne', Real.log_exp]
  linarith [Real.log_le_sub_one_of_pos hn]

private lemma uniform_height_cubic {p s : ℝ} (hp : 1 ≤ p) (hs : 0 ≤ s) (hs₂ : s ≤ 2)
    (q : ℝ≥0∞) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) {N : ℕ} (hN : 1 ≤ N) :
    (Hunif A B (nuHat p s) (kapHat p s q 0) N : ℝ) + 1 ≤ 12 * A * (B + 1) * (N : ℝ) ^ 3 := by
  have hν : nuHat p s ≤ 2 := by
    have hp₁ : 1 / p ≤ 1 := (div_le_one (by linarith)).mpr hp
    unfold nuHat
    split_ifs
    · exact max_le (by norm_num) hs₂
    · linarith
    · norm_num
  have hκ : kapHat p s q 0 ≤ 1 := by
    unfold kapHat
    split_ifs <;> simp [thetaQ_le_one]
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL := one_le_Lfun hN
  have h₁ : ((N : ℝ) + 1) ^ nuHat p s ≤ (2 * (N : ℝ)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow_of_exponent_le (by linarith) (show nuHat p s ≤ (2 : ℕ) from hν)).trans
      (Real.rpow_le_rpow (by positivity) (by linarith) (by positivity))
  have h₂ : Lfun N ^ kapHat p s q 0 ≤ N :=
    (Real.rpow_le_rpow_of_exponent_le hL hκ).trans (by simpa using Lfun_le_nat hN)
  have hceil : (Hunif A B (nuHat p s) (kapHat p s q 0) N : ℝ) <
      A * (B + 1) * ((N : ℝ) + 1) ^ nuHat p s * Lfun N ^ kapHat p s q 0 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hprod : A * (B + 1) * ((N : ℝ) + 1) ^ nuHat p s * Lfun N ^ kapHat p s q 0 ≤
      A * (B + 1) * ((2 * (N : ℝ)) ^ 2) * N :=
    mul_le_mul (mul_le_mul_of_nonneg_left h₁ (by positivity)) h₂ (by positivity) (by positivity)
  have hx : 1 ≤ A * (B + 1) * (N : ℝ) ^ 3 :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hA (by linarith)) (one_le_pow₀ hn)
  nlinarith only [hceil, hprod, hx]

private lemma width_le_logarithms {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) {N H : ℕ}
    (hN : 1 ≤ N) (hH : (H : ℝ) + 1 ≤ 12 * A * (B + 1) * (N : ℝ) ^ 3) :
    (coordinateWidth H : ℝ) + 1 ≤
      ((Real.log (12 * A) / Real.log 2 + 2) / Real.log 2 + 3 / Real.log 2) *
        (Real.log N + Real.log (B + 1)) := by
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLA : 0 ≤ Real.log (12 * A) := Real.log_nonneg (by linarith)
  have hn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN₁
  have hb : Real.log 2 ≤ Real.log (B + 1) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog := Real.log_le_log (by positivity) hH
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  norm_num at hlog
  have hw : (coordinateWidth H : ℝ) < Real.logb 2 ((H : ℝ) + 1) + 1 := by
    rw [coordinateWidth_eq]
    exact Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg _)))
  rw [Real.logb] at hw
  let x := Real.log N + Real.log (B + 1)
  let d := Real.log (12 * A) / Real.log 2 + 2
  have hx : Real.log 2 ≤ x := by dsimp [x]; linarith
  have hd : 0 ≤ d / Real.log 2 := by dsimp [d]; positivity
  have hx₀ : d ≤ (d / Real.log 2) * x := by
    calc d = d / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hx hd
  have hy : Real.log ((H : ℝ) + 1) / Real.log 2 ≤ (Real.log (12 * A) + 3 * x) / Real.log 2 := by
    apply div_le_div_of_nonneg_right _ hlog2.le
    dsimp [x]
    linarith
  calc (coordinateWidth H : ℝ) + 1 ≤ d + (3 / Real.log 2) * x := by
        dsimp [d]
        have he : (Real.log (12 * A) + 3 * x) / Real.log 2 =
            Real.log (12 * A) / Real.log 2 + (3 / Real.log 2) * x := by ring
        rw [he] at hy
        linarith
    _ ≤ _ := by rw [add_mul]; exact add_le_add_left hx₀ _

/-- Corolário de taxa e bits, com uma constante independente do raio e da função. -/
theorem uniform_rate_bits {p s : ℝ} (hp : 1 ≤ p) (hs : 0 < s) (hs₂ : s < 2)
    {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ CW Cs c : ℝ, 0 ≤ CW ∧ 1 ≤ Cs ∧ 0 < c ∧
      ∀ B : ℝ, 1 ≤ B → ∀ f : ℝ → ℝ, Measurable f →
        besovNorm (ENNReal.ofReal p) s q f ≤ ENNReal.ofReal B →
        ∀ r : ℕ, 1 ≤ r →
          let n : ℕ := 2 ^ r
          let H := Hunif (32 * (Cs + 1)) B (nuHat p s) (kapHat p s q 0) n
          ∃ g : boundedLibrary n H,
            distP (ENNReal.ofReal p) f g ≤
              ENNReal.ofReal ((9 * CW * B + 1) * (n : ℝ) ^ (-s)) ∧
            ((libraryWord g).length : ℝ) ≤ c * n * (Real.log n + Real.log (B + 1)) := by
  obtain ⟨CW, Cs, hCW, hCs, hunif⟩ := uniform_besov_ball (s := s) hp hq hs₂
  have happ := (hunif 0 le_rfl).1
  let A := 32 * (Cs + 1)
  have hA : 1 ≤ A := by dsimp [A]; linarith
  let d := (Real.log (12 * A) / Real.log 2 + 2) / Real.log 2 + 3 / Real.log 2
  have hd : 0 < d := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 12 * A by linarith)
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    dsimp [d]
    positivity
  refine ⟨CW, Cs, 4 * d, hCW, hCs, by positivity, fun B hB f hf hb r hr ↦ ?_⟩
  dsimp only
  let n : ℕ := 2 ^ r
  let H := Hunif A B (nuHat p s) (kapHat p s q 0) n
  have hn : 1 ≤ n := Nat.one_le_two_pow
  obtain ⟨g, hg, hD, hE, _⟩ := happ B hB f hf hb r hr
  let g' : boundedLibrary n H := ⟨g, Or.inr hg⟩
  refine ⟨g', ?_, ?_⟩
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using hD.trans hE
  · have hword := (boundedLibrary_code n H hn).1 g'
    have hwidth := width_le_logarithms hA hB hn (uniform_height_cubic hp hs.le hs₂.le q hA hB hn)
    calc ((libraryWord g').length : ℝ) ≤ 4 * n * ((coordinateWidth H : ℝ) + 1) := by
          exact_mod_cast hword
      _ ≤ (4 * n) * (d * (Real.log n + Real.log (B + 1))) :=
          mul_le_mul_of_nonneg_left hwidth (by positivity)
      _ = _ := by
        change (4 * (n : ℝ)) * (d * (Real.log n + Real.log (B + 1))) =
          4 * d * n * (Real.log n + Real.log (B + 1))
        ring

end FormalizacaoBits
