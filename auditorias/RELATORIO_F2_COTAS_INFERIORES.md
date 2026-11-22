# Relatório F2 — Cotas inferiores do Teorema 5.2 em Lean 4

**Resultado central:** `FormalizacaoLeaf.leaf_floor_const` (`lean4/formalizacao/Formalizacao/LeafFloor.lean:433`) demonstra, sem `sorry` e sem hipóteses auxiliares, o piso pelo número de folhas `D_{p,s,q}(N,H) ≥ c_leaf·N^{-s}` para todo `1≤p<∞`, `0<s<2`, `0<q≤∞` e todos os inteiros `N,H≥2`, com `c_leaf = c(p,s,q) > 0` escolhido antes de `N,H`.

---

## 1. Estado inicial da branch

| Item | Valor |
|---|---|
| Branch | `formalizacao-teorema-5-2` |
| Commit de referência da F1 | `03182468250d1bd8a88612d73868f1fbcaf58725` |
| Checkpoint F2.1 (`MinimaxDefs.lean`) | `84f3365` |
| Checkpoint F2.2 (`Packing.lean`) | `f1d717b` |
| Tag `editorial-v1.0` | `f02baea` (inalterada) |
| `pesquisa-minimax-altura`, `main` | não alteradas |

## 2. Arquivos criados e modificados

| Arquivo | Situação |
|---|---|
| `lean4/formalizacao/Formalizacao/MinimaxDefs.lean` | novo (80 linhas) |
| `lean4/formalizacao/Formalizacao/Packing.lean` | novo (~630 linhas) |
| `lean4/formalizacao/Formalizacao/LeafFloor.lean` | novo (~510 linhas) |
| `lean4/formalizacao/Formalizacao.lean` | +3 imports |
| `lean4/formalizacao/Formalizacao/Auditoria.lean` | +27 consultas `#print axioms` |
| `lean4/formalizacao/auditoria_axiomas.txt` | regenerado a partir da saída efetiva (228 linhas) |
| `auditorias/RELATORIO_F2_COTAS_INFERIORES.md` | este relatório |

Nenhum LaTeX, PDF, mapa, módulo Lean preexistente, `Pendencias/` ou `RequestProject/` foi alterado.

## 3. Definição Lean de `Dfun`

`FormalizacaoMinimax.Dfun` (`MinimaxDefs.lean:28`):

```lean
noncomputable def Dfun (p s : ℝ) (q : ENNReal) (N H : ℕ) : ENNReal :=
  ⨆ (f : ℝ → ℝ) (_ : Measurable f) (_ : besovNorm (ENNReal.ofReal p) s q f ≤ 1),
    bestError (ENNReal.ofReal p) N H f
```

Preserva: funções mensuráveis; a quase-norma de Besov (`besovNorm`, `UnifSup.lean:23`) na bola unitária; erro em `L^p([0,1])` por `distP`; orçamentos `N`,`H` independentes (`bestError` usa `Sigma (fun _ ↦ H) N`); inclusão do aproximante zero (`Sigma = {0} ∪ …`); convenções de `ℝ≥0∞`. Não usa `JointBudget` (norma uniforme).

Não é trivial por coerção ou domínio vazio: o piso `leaf_floor_const` e os pisos de altura (§12) fornecem funções-teste explícitas na bola com erro positivo.

Lemas estruturais: `le_Dfun` (`:68`) introduz uma cota inferior a partir de um `f` mensurável na bola; `le_bestError_of_forall` (`:75`) converte um limite inferior válido para todo `g ∈ Σ_{N,H}` em limite para o ínfimo.

## 4. Definição de `aPS`

`FormalizacaoMinimax.aPS` (`MinimaxDefs.lean:22`): `if s < 1/p then 1+1/p-s else if s ≤ 1 then 1 else s`. Lemas: `aPS_of_lt` (`:32`), `aPS_of_mid` (`:36`), `aPS_of_gt` (`:40`), `aPS_pos` (`:47`).

## 5. Equivalência `aPS = nuHat` (F1-GAP-005)

`aPS_eq_nuHat` (`MinimaxDefs.lean:57`): para `1 ≤ p`, `aPS p s = nuHat p s`, para todo `s` (portanto no domínio `0<s<2` do teorema). Demonstrada por análise de casos, não por substituição de definições.

## 6. Construção da família de bumps

Função-teste fixa: `φB` (`AlturaFloor.lean`), suave, com suporte em `(1/8,5/8) ⊂ (0,1)`. Soma de bumps `Fm m A x = A · Σ_{j<m} φB(m x − j)` (`Packing.lean:131`). A escolha de `φB` fixa a função-teste `φ` do manuscrito; as constantes dependem de `φB` fixa e de `(s,q)`.

Fatos demonstrados: identidade de escala `diff2_scaled` (`:37`); **overlap ≤ 3** `overlap_le_three` (`:49`): para cada `x` e `u`, no máximo três `j<m` têm `D2 u φB (m x − j) ≠ 0`; `abs_sum_bump_le`: no máximo um termo de `Σ_j φB(m x − j)` é não nulo; `Fm_on_cell` (`LeafFloor.lean`): na célula `(j/m,(j+1)/m)` só o bump `j` é não nulo.

## 7. Normalização de Besov (F1-GAP-003)

Estratégia (distinta da escala `‖f_m''‖_p` do manuscrito, com o mesmo efeito):

1. `diff2_Fm_pow_le` (`:145`): `|Δ²_h f_m(x)|^p ≤ 3^{p-1}|A|^p Σ_j |D2 (mh) φB (m x − j)|^p`, pelo overlap ≤ 3 e desigualdade de potência (`sum_rpow_le_three`). **Não há fator proporcional a `m`.**
2. `lint_diff_le` (`:183`): integrando e mudando variável (`lint_affine`), `∫|Δ²_h f_m|^p ≤ 3^{p-1}|A|^p · ∫|D2 (mh) φB|^p`: os `m` termos cancelam o fator `m⁻¹` da mudança de variável.
3. `Ipow_small_le`: para `0≤u≤1`, `∫|D2 u φB|^p ≤ 3 (M u²)^p` (suporte em `[-2,1]`, `|D2|≤M u²`).
4. `exists_K0` (`:337`): `ω_p(f_m,t) ≤ K0·|A|·min{1,(mt)²}`, com **`K0` independente de `p`, `m`, `A`, `t`**. Caso `mt<1` por (1)–(3); caso `mt≥1` por `wtP_le_four` e `‖f_m‖_p ≤ |A|`.
5. `aTerm_le_low`/`aTerm_le_high` (`:417`, `:443`): com `k = ⌊log₂ m⌋`, `m^{-s}2^{rs}min{1,(m2^{-r})²} ≤ (2^{-s})^{k-r}` se `r≤k` e `≤ (2^{-(2-s)})^{r-k-1}` se `r>k`.
6. `exists_Lq` (`:541`): `‖(2^{rs}ω_p(f_m,2^{-r}))_r‖_{ℓ^q} ≤ b·L`, com `L` dependente só de `(s,q)`. Usa `tsum_split_le` e `lqNorm_le_of_pow_sum` de `AlturaBesov.lean`. Casos `q=∞` (supremo, termos `≤1`) e `q<∞` (série geométrica). **Cobre `0<q<1`**: `lqNorm_le_of_pow_sum` só exige `0<q`, `q≠⊤`.
7. `packing_norm_le` (`:601`): existe `b>0`, escolhido antes de `m`, com `‖f_m‖*_{B^s_{p,q}} ≤ 1` para todo `m ≥ 1`.

## 8. Lemas combinatórios de contagem (F1-GAP-004, parte 1)

- `splits` (`LeafFloor.lean:20`): pontos médios dos nós internos da árvore.
- `card_splits_le` (`:25`): `|splits| + 1 ≤ numLeaves`, por indução na árvore.
- `affine_on_open` (`:55`): em todo intervalo aberto contido na célula raiz e sem pontos de divisão, `T.eval` é afim. Cobre fronteiras que coincidem com extremos de células de teste (que não pertencem ao intervalo aberto) e folhas que cruzam várias células.
- `exists_good_cells` (`:105`): com `m=2N`, para todo `g ∈ Σ_{N,H}` existem `≥ N` células de teste onde `g` é afim; cobre o aproximante zero e árvores adaptativas arbitrárias. Não depende de `H`.

## 9. Estimativa inferior local (F1-GAP-004, parte 2)

`L1_affine_cell` e `lp_lower_cell` (versões gerais de `L1_affine_interval` e `lp_lower_of_L1`, sem a restrição `c+t=1`), e `cell_lower` (`:258`): numa célula onde `g` é afim, `‖f_m−g‖_{L^p(I_j)} ≥ (Aκ/M)·m^{-1/p}`. Vale para todo `p≥1`, inclusive `p=1` (usa `p'=∞` via `eLpNorm_le_eLpNorm_mul_rpow_measure_univ`). Não assume afinidade global.

## 10. Agregação das células

`agg_lower` (`:341`): `c0^p·|G| ≤ ‖F‖_{L^p([0,1])}^p` para `|G|` células de teste disjuntas, por `lintegral_biUnion_finset`. `leaf_dist_lower` (`:380`): para todo `g ∈ Σ_{N,H}`, `‖Fm(2N)A − g‖_{L^p} ≥ Aκ/(2M)`.

## 11. Demonstração de `leaf_floor_const`

`leaf_floor_const` (`LeafFloor.lean:433`):

```lean
theorem leaf_floor_const {p s : ℝ} {q : ℝ≥0∞} (hp : 1 ≤ p) (hs0 : 0 < s) (hs2 : s < 2)
    (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ N H : ℕ, 2 ≤ N → 2 ≤ H →
      ENNReal.ofReal (c * (N : ℝ) ^ (-s)) ≤ FormalizacaoMinimax.Dfun p s q N H
```

Prova: `b` de `packing_norm_le`; `m=2N`, `A=b·m^{-s}`; `f=Fm m A` está na bola e é mensurável; para todo `g∈Σ`, `leaf_dist_lower` dá erro `≥ Aκ/(2M)`; `A = b·2^{-s}·N^{-s}`. Constante: `c = b·2^{-s}·κ/(2M)`, onde `κ = ∫(φB')²` e `M ≥ sup|φB''|`. Depende de `(p,s,q)` através de `b` (que depende de `(s,q)` e de `φB` fixa); não depende de `N`, `H`, da árvore nem de `g`.

## 12. Reutilização dos pisos de altura

Assinaturas inspecionadas e pontes demonstradas em `LeafFloor.lean`:

| Ponte | Piso original | Resultado para `Dfun` |
|---|---|---|
| `dfun_geometric_floor` (`:466`) | `geometric_floor` | `ofReal(c·H^{-s}) ≤ Dfun p s q N H` |
| `dfun_slope_floor` (`:478`) | `slope_floor` (`s≤1/p`) | `ofReal(c·H^{-s/(1+(1/p−s))}) ≤ Dfun …` |
| `dfun_arithmetic_floor` (`:496`) | `arithmetic_floor_lp` | `ofReal(1/(2H)) ≤ Dfun …` |

Os pisos originais não foram modificados.

## 13. Matriz de fidelidade LaTeX–Lean

| Item exigido | Verificação |
|---|---|
| Mesma bola unitária | `besovNorm ≤ 1` com `‖f‖* = ‖f‖_p + ‖(2^{rs}ω_p(f,2^{-r}))_{r≥0}‖_{ℓ^q}` (`lp:eq:besov-p`) |
| Mesma norma de erro | `distP` em `L^p([0,1])` |
| Mesmo conjunto de aproximantes | `Sigma (fun _ ↦ H) N = {0} ∪ 𝒜_{N,H}` |
| Mesma altura aritmética | herdada de `Atom.height` (F1 §4); não usada na prova do piso de folhas |
| Mesmo orçamento de folhas | `AdmNH N H T` (`numLeaves ≤ N`) |
| Árvores adaptativas | `exists_good_cells`/`affine_on_open` valem para toda `LTree` com `WF` |
| Constantes uniformes | `c` escolhido antes de `N,H`; independente da árvore e de `g` |
| `p=1` | coberto por `lp_lower_cell` |
| `0<q<1` | coberto por `exists_Lq` |
| `q=∞` | coberto por `exists_Lq` (ramo `q=⊤`) |

Divergências: (i) usa-se `φB` específica no lugar de `φ ∈ C_c^∞((0,1))` genérica (escolha de uma função-teste fixa, compatível com o enunciado existencial); (ii) a estimativa do módulo usa overlap ≤ 3 em vez da escala `‖f_m''‖_p`.

## 14. Compilação

`lake build Formalizacao`: sucesso (8136 jobs, sem erros). `lake build Formalizacao.MinimaxDefs`, `.Packing`, `.LeafFloor` compilados individualmente durante o desenvolvimento.

## 15. Auditoria de axiomas

`lake env lean Formalizacao/Auditoria.lean`: 228 consultas, todas com `[propext, Classical.choice, Quot.sound]`; 0 ocorrências de `sorryAx`. `diff` contra `auditoria_axiomas.txt` (regenerado a partir da saída efetiva): vazio. As 201 linhas anteriores permanecem idênticas.

Varredura de `sorry`, `admit`, `axiom`, `opaque` nos três módulos novos: 0 ocorrências.

## 16. Testes executados

`python3 -B -m unittest discover -s testes -v`: 9 testes, OK. `python3 mapas/verificar_mapa.py`: 64 entradas, 263 nomes Lean localizados, mapa atualizado. Nenhuma alteração no mapa foi necessária.

## 17. Lacunas F1 resolvidas

| Lacuna | Situação |
|---|---|
| F1-GAP-001 | Resolvida: `aPS`, `Dfun`. |
| F1-GAP-002 | Resolvida: `leaf_floor_const`. |
| F1-GAP-003 | Resolvida: `packing_norm_le` (com `exists_K0`, `exists_Lq`). |
| F1-GAP-004 | Resolvida: `exists_good_cells`, `cell_lower`, `agg_lower`, `leaf_dist_lower`. |
| F1-GAP-005 | Resolvida: `aPS_eq_nuHat`. |

## 18. Pendências restantes

- **F1-GAP-006** (composição `max(piso_folhas, piso_altura) ≥ ½·soma` por regime de `s`): pertence à F5. Os componentes estão prontos (§12 e `leaf_floor_const`).
- **F1-GAP-007 a 011** (quantização por nó, `p=s=1` com `q>1`, `s=1/p` com `q=∞`, independência de `(N,H)`, ponte para o supremo): F3 e F4, não iniciadas.
- F1-GAP-012 a 019: inalteradas.

## 19. Critérios de prontidão

- **F3 pode começar:** sim. Não depende de F2.
- **Cota inferior pronta para F5:** sim. Estão demonstrados `leaf_floor_const` e os três pisos de altura em forma de `Dfun`. A composição final depende apenas de aritmética real: `max ≥ ½·soma`, e escolha do piso de altura por faixa de `s` (`slope` para `s<1/p`, `geometric` para `1/p≤s≤1`, `arithmetic` para `s>1`; para `1<s<2`, `H^{-s/a}=H^{-1}`).
- A F2 não demonstra o Teorema 5.2 completo; entrega a base inferior.
