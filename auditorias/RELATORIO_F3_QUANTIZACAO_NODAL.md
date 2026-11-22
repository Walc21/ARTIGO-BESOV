# F3 — Quantização nodal e altura linear em Lean 4

A etapa parte de `472fdbee98303cb6c7043b71fe0ce50196054ab7` na branch
`formalizacao-teorema-5-2`. Os dois resultados fecham as lacunas F1-GAP-007 e F1-GAP-008.
O checkpoint F3.1 é `35b488d9dc5e55a658cc6e9d54d0b23eee359108`.
O checkpoint F3.2 contém este relatório.

| Etapa | Referência LaTeX | Declaração Lean |
|---|---|---|
| F3.1 | [`lp:lem:nodal-variable-height`](../conjecturas_lp.tex#L447) | [`FormalizacaoAltura.nodal_variable_height`](../lean4/formalizacao/Formalizacao/NodalVariable.lean) |
| F3.2 | [`lp:prop:l1-linear-height`](../conjecturas_lp.tex#L649) | [`FormalizacaoAltura.l1_linear_height`](../lean4/formalizacao/Formalizacao/L1LinearHeight.lean) |

## F3.1 — Fidelidade da quantização

- Os parâmetros são `r ≥ 1`, `n = 2^r`, `J ≥ 0`, `H : ℕ`, os `n+1` dados nodais e a cota `|y(j+1) − y(j)| ≤ J` para `j < n`. A condição `8 max_j w_j ≤ H` é escrita na forma equivalente `∀ j ≤ n, 8w_j ≤ H`, com `w_j = 1 + J + |y_j|`. A segunda condição é `n(J+4) ≤ H`.
- A escolha de cada grade satisfaz `8w_j Q_j ≤ H < 16w_j Q_j`, com `Q_j = 2^(e_j)`. O arredondamento dos pares é feito na própria grade. Cada nó ímpar dispõe de três candidatos e evita os dois valores pares adjacentes. Todo erro nodal é limitado por `2/Q_j ≤ 2` e por `32w_j/H`.
- Em cada folha, ambos os valores são escritos com denominador `D = max(Q_j,Q_{j+1})`. Com `w = min(w_j,w_{j+1})`, os numeradores têm módulo no máximo `3Dw` e `8Dw ≤ H`. O valor central tem numerador de módulo no máximo `6Dw` e denominador `2D`. Para `n ≤ D`, a inclinação tem denominador `D/n` e numerador de módulo no máximo `6Dw`. Para `D < n`, ela é inteira e tem módulo no máximo `n(J+4)`. A altura das frações reduzidas é controlada por `ht_div_le_nat`.
- A árvore `uniformTree` tem exatamente `n` folhas. A distinção dos valores adjacentes garante inclinações não nulas. A condição `WF` garante a colagem, e o enunciado inclui `ContinuousOn g (Icc 0 1)`. A pertença a `classNH n H` certifica o orçamento completo, inclusive os índices das folhas.
- A hipótese sobre `u` identifica o interpolante afim em cada célula fechada. A integral local da interpolação dos módulos é a soma dos dois erros nodais dividida por `2n`. Cada nó contribui no máximo duas vezes na soma, o que dá `distP 1 u g ≤ ofReal (32/(Hn) · Σⱼ w_j)`. O uso de `ℝ≥0∞` é o da norma `distP` existente.

## F3.2 — Fidelidade da cota em `B¹_{1,q}`

- `whitney_lp` fornece `C_W` para `p = 1`. A prova usa `C_J = 32 + 576 C_W`, `J = C_J B` e escolhe `C_E = 320 + 64 C_J` antes de `q, B, f, r, H`. O raio satisfaz `B ≥ 1`, e a bola usa `besovNorm 1 1 q f` para representantes mensuráveis, como em `Dfun`. A hipótese `0 < q` inclui `q = ⊤`.
- A estimativa local `abs_lam_le` dá `|λ_j| ≤ 4n ‖f‖_{L¹(I_{c(j)})}`. As integrais das células somam a integral em `[0,1]`, e somente a última célula entra duas vezes na soma nodal. Seguem `max_j |λ_j| ≤ 4nB` e `Σⱼ |λ_j| ≤ 8n ‖f‖₁`. No nível base, as duas funções chapéu dão `|Q₂ f| ≤ 8 ‖f‖₁`.
- A bola controla cada termo diádico do módulo por `B`. Com `vk_slope_le`, a inclinação da diferença de níveis é limitada por `K_k = 288 C_W B · 2^(k+1)`. O lema `nodal_jump` dá a contribuição de base de até `32B` e a contribuição geométrica de até `576 C_W B`.
- A hipótese `H ≥ C_E(B+1)n` implica diretamente as duas condições de F3.1. A média dos pesos é limitada por `2(1+J)+8B`, e `32[2(1+J)+8B] ≤ C_E(B+1)`. Aplicando F3.1 a `Qₙ f` e somando a estimativa `quasi_error`, resulta
  `distP 1 f g ≤ 9·ofReal(C_W)·wtP 1 (1/n) f + ofReal(C_E(B+1)/H)` para algum `g ∈ classNH n H`.

## Verificação

| Verificação | F3.1 | F3.2 |
|---|---|---|
| Compilação do módulo e `lake build Formalizacao` | Sucesso, 8137 jobs no build | Sucesso, 8138 jobs no build |
| `lake env lean Formalizacao/Auditoria.lean` | 229 declarações, incluindo F3.1 | 230 declarações, incluindo F3.1 e F3.2 |
| Axiomas transitivos | `propext`, `Classical.choice`, `Quot.sound` | Idem |
| `python3 -B -m unittest discover -s testes -v` | 9 testes passaram | 9 testes passaram |
| `python3 mapas/verificar_mapa.py` | 64 entradas e 263 nomes verificados pelo Lean | Idem |

A regressão em Lean também compilou dois exemplos. O primeiro usa `n = 2`, dados nodais
nulos e `H = 8`, com igualdade nas duas condições de altura. O segundo instancia a mesma
escolha de `C_W, C_E` em `q = 1/2` e `q = ∞` para a bola unitária com
`H = ⌈4 C_E⌉`.

A saída de axiomas de F1 e F2 foi preservada e as novas consultas foram acrescentadas ao
[registro de axiomas](../lean4/formalizacao/auditoria_axiomas.txt). Os novos módulos têm zero
`sorry`, `admit` ou axiomas locais. Os avisos do build integral vêm de módulos preexistentes.

A F3 entrega os dois resultados sem bloqueadores matemáticos. A F4 tem a dependência relativa
a `p = s = 1` disponível e pode começar em uma próxima etapa.
