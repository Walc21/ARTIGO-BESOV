# F4 — Cota superior em folhas e altura

A etapa parte de `be6497a55672e58eba7db7c8badd4da791e02bd6` na branch
`formalizacao-teorema-5-2`. O HEAD local e o HEAD remoto coincidiam e a árvore estava limpa.
A cota superior de `lp:thm:minimax-nh` é demonstrada em
[`FormalizacaoMinimax.upper_bound_NH`](../lean4/formalizacao/Formalizacao/MinimaxUpper.lean),
para o funcional `Dfun` da F2.

## Construção por escala

`upper_bound_dyadic` escolhe constantes reais `A ≥ 1` e `C > 0` antes do alvo, do nível
`r ≥ 1` e da altura `H`. Para toda função mensurável na bola unitária e `n = 2^r`,
se `A n^(aPS p s) ≤ H`, há um aproximante em `classNH n H` com erro em Lᵖ de até `C n^(-s)`.

| Regime | Potência da altura | Construção para todo `0 < q ≤ ∞` |
|---|---|---|
| `0 < s < 1/p` | `1 + 1/p − s` | Conclusão pontual de `uniform_besov_ball` com `κ = 0`. |
| `1/p < s ≤ 1` | `1` | Mesma conclusão, com amplitude nodal uniforme. |
| `1 < s < 2` | `s` | Mesma conclusão, com a potência da altura dada por `aPS_eq_nuHat`. |
| `s = 1/p`, `p > 1` | `1` | `critical_upper_dyadic` aplica `critical_dist` à altura `H` disponível. |
| `p = s = 1` | `1` | `l1_linear_height` com raio 1 e `H ≥ 2 C_E n`. |

`critical_dist` extrai de `critical_level` o erro em Lᵖ do aproximante de `critical_approx`.
Ambas as provas reutilizam a mesma estimativa de quase-interpolação e a mesma quantização.
Em `critical_upper_dyadic`, o controle de um termo pela norma ℓᵠ vale para `q = ∞`.
A estimativa `E_majorant` controla o erro de quantização multiplicado por `n^(1/p)` por um
múltiplo de `(r+2) ρ^r` com `ρ = 2^(1/p−1) < 1`. O lema `poly_geom_majorant`, aplicado
com segunda base 1, fornece uma constante uniforme. O fator de nível ocorre no erro
intermediário, e a altura exigida permanece linear.

## Orçamentos independentes

Com `Y = (H/A)^(1/aPS p s)` e `X = min(N,Y)`, `exists_dyadic_scale` escolhe
`r = ⌊log₂ X⌋` para `X ≥ 2` e prova `X/2 < 2^r ≤ X`. Daí `2^r ≤ N` e
`A (2^r)^(aPS p s) ≤ H`. Os lemas `classNH_mono` e `sigma_const_mono` formalizam
a inclusão das classes quando se aumentam os orçamentos. Se `X < 2`, então `Y < 2`
porque `N ≥ 2`. Nesse ramo o candidato zero tem erro de até 1 na bola, e
`1 ≤ 2^s Y^(-s)`.

A identidade `Y^(-s) = A^(s/aPS p s) H^(-s/aPS p s)` permite usar em ambos os ramos
a mesma constante, `2^s (C+1) A^(s/aPS p s)`, escolhida antes de `N,H`.
A prova toma o ínfimo sobre os candidatos e o supremo sobre a bola unitária em
`ℝ≥0∞`. O enunciado usa os mesmos expoentes, orçamentos e quase-norma do manuscrito.

## Verificação

- `lake build Formalizacao` concluiu com sucesso com 8139 jobs. O build reportou
  avisos preexistentes.
- `python3 -B -m unittest discover -s testes -v` executou 9 testes com sucesso.
- O Lean executou as sete novas consultas transitivas de `Auditoria.lean`, com
  somente `propext`, `Classical.choice` e `Quot.sound` em cada uma. O registro
  atualizado preserva as 230 consultas anteriores e tem zero ocorrências de `sorryAx`.
- A varredura dos dois módulos da prova encontrou zero ocorrências de
  `sorry`, `admit`, `axiom` ou `opaque`.
- O mapa LaTeX–Lean passou na verificação após a atualização do número de linha
  de `critical_level`.

A composição com os pisos inferiores pertence à F5. A auditoria independente fica para a F6.
