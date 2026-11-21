# Auditoria da integração

Em 21 de novembro de 2026, a branch local `integracao-auditoria` partiu de
`6e74ba024f772be74189e36ed5e28212e72372bc`, commit confirmado na `main`
local e no remoto. A revisão matemática (`origin/codex/revisao-matematica`,
`321f1f9e6832b873bac91751ceb2967aa86dd254`) entrou por avanço direto.
Em seguida, a revisão editorial (`origin/revisao-editorial`,
`1cb00aecceb02e6ec3fbd44a64617cc900412cc3`) entrou por merge, preservando
os dois commits de origem no histórico.

## Resolução do conflito

O único conflito foi em `conjecturas_lp_referencias.tex`. A revisão
matemática acrescentou Kerkyacharian–Picard (2003) imediatamente antes da
entrada de Kolomoitsev–Tikhonov, que a revisão editorial atualizou.

- Mantive a bibliografia editorial integral, incluindo a versão publicada de
  Kolomoitsev–Tikhonov no *Journal of Approximation Theory* (2020,
  DOI `10.1016/j.jat.2020.105423`) e o link do preprint. A chave
  `lp-kolomoitsev2019` foi mantida, com o ano de citação atualizado para 2020.
- Insertei a entrada de Kerkyacharian–Picard (2003, DOI `10.1051/ps:2003011`)
  da revisão matemática antes de Kolomoitsev–Tikhonov.
- O Git combinou automaticamente as alterações em `conjecturas_lp.tex`,
  `conjecturas_lp_en.tex` e `conjecturas_lp_citacoes.tex`. As citações
  incluem Kerkyacharian–Picard, DeVore–Popov (1988a e 1988b),
  Petrushev–Popov (1987) e Kolomoitsev–Tikhonov (2020).

## Verificações

- Confirmei a presença dos patches completos das duas revisões no índice
  com `git apply --cached --check --reverse --unidiff-zero`, incluindo
  as alterações de citações e bibliografia.
- `git diff --cached --check` passou. O índice ficou sem entradas em
  conflito e a busca por marcadores de conflito nos arquivos TeX ficou vazia.
- Os PDFs versionados e o mapa TeX–Lean foram incorporados como vieram da
  revisão matemática. As compilações LaTeX e Lean 4 e a verificação dos
  arquivos gerados ficam para uma etapa posterior.

A integração ocorreu exclusivamente na cópia de integração, na branch
`integracao-auditoria`, sem push ou alterações na `main` ou nas pastas dos
agentes A e B.
