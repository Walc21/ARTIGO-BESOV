# Validação da integração

21 de novembro de 2026 · branch `integracao-auditoria`

A [auditoria da integração](AUDITORIA_INTEGRACAO.md) registrou o merge das revisões matemática e editorial. A primeira validação encontrou duas falhas na seleção de alvos do Lake, três PDFs versionados anteriores à revisão editorial, uma página final com duas linhas na edição ABNT e o mapa TeX–Lean desatualizado. Este relatório registra as correções e a verificação posterior.

**Resultado.** As verificações técnicas finais passaram e a branch está pronta localmente para um pull request. Permanecem os avisos preexistentes do Lean, os dados editoriais pendentes e as questões matemáticas descritas abaixo.

## Git e escopo

O trabalho partiu do merge `1601825482259475abaa944fb61ceabd98055308`, com os pais `321f1f9e6832b873bac91751ceb2967aa86dd254` (revisão matemática) e `1cb00aecceb02e6ec3fbd44a64617cc900412cc3` (revisão editorial). A validação anterior confirmou os dois patches integrados, o índice sem conflitos e a árvore Lean idêntica à revisão matemática. A `main` local e a referência local `origin/main` apontavam para `6e74ba024f772be74189e36ed5e28212e72372bc`.

A etapa final preserva os dois pais do merge e todos os 162 fontes Lean rastreados, inclusive seus enunciados e demonstrações. Os únicos ajustes de LaTeX estão no apêndice em português. Os três PDFs de `output/pdf/` são evidência da primeira validação e ficam locais. O commit inclui os PDFs atualizados da raiz, usados pelos links do README. O trabalho ocorreu na cópia de integração, com a `main` e as cópias dos agentes A e B intactas. A publicação e o merge para a `main` ficam fora desta etapa.

## Lean 4

A primeira validação reproduziu `no such file or directory` para `RequestProject.lean` e `Pendencias.lean` quando o Lake recebeu os nomes das bibliotecas. Os dois caminhos estão ausentes do histórico consultado e nenhum fonte local importa esses nomes sozinhos. No [lakefile.toml](lean4/formalizacao/lakefile.toml), os seletores exatos foram retirados e os globs `RequestProject.+` e `Pendencias.+` continuam a incluir todos os submódulos. `Formalizacao` continua como alvo padrão.

Usei o Lean 4.28.0 (`7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`) e Lake `5.0.0-src+7e01a1b`. A primeira validação já havia copiado os pacotes pré-compilados para dentro da integração, isolando-os das duas cópias de origem. Na etapa final conferi as nove revisões pelo manifesto, inclusive Mathlib v4.28.0 (`8f9d9cff6bd728b17a24e163c9402775d9e6a365`), e os diretórios Git estavam limpos. Arquivei o `.lake/build` local antes da recompilação e reutilizei apenas os artefatos das dependências de `.lake/packages`. O sandbox estava sem rede e o manifesto e a versão do toolchain conferiram com o merge.

| Execução | Resultado | Módulos locais compilados nessa execução | Avisos |
|---|---|---:|---:|
| `lake build` | Passou, 8.133 jobs | 107 | 90 |
| `lake --no-cache build Formalizacao RequestProject Pendencias +Formalizacao.Auditoria` | Passou, 8.190 jobs | 55 | 116 |
| `lake --no-cache build` com os 85 módulos auxiliares explícitos | Passou, 8.110 jobs | 0, todos já compilados nas duas execuções anteriores | 36 |

Os dois primeiros builds compilaram os 162 fontes, todos com `.olean`, incluindo os 85 auxiliares (31 em `RequestProject` e 54 em `Pendencias`) e `Formalizacao.Auditoria`. A terceira execução também confirmou os 85 como alvos explícitos. O conjunto dos 116 avisos distintos nos três logs coincide com o da validação anterior. São depreciações e avisos de linter, incluindo variáveis, argumentos e táticas sem uso. A varredura dos 162 arquivos com o `lean4-skills-sorry-analyzer` encontrou zero `sorry`. A busca complementar encontrou duas menções documentais e nenhuma declaração de `axiom` ou uso de `admit` nos fontes locais.

O alvo `Formalizacao.Auditoria` reproduziu as 201 linhas de `auditoria_axiomas.txt` para 196 declarações distintas. Uma varredura complementar, com `Lean.CollectAxioms.collect`, percorreu as dependências de 5.863 constantes atribuídas aos 162 módulos do projeto no ambiente Lean. O conjunto resultante foi `propext`, `Classical.choice` e `Quot.sound`.

## LaTeX e PDFs

Compilei as três edições com `latexmk` 4.88 e pdfTeX 1.40.29 (TeX Live 2026/Debian). Em cada rodada, cada edição convergiu em três passagens. Os avisos transitórios de referências cruzadas ficaram restritos às passagens intermediárias. Os logs finais ficaram sem erros, avisos ou caixas `Overfull` e `Underfull`. O `qpdf --check` passou para todos os PDFs.

Na edição ABNT, o espaço reservado antes do segundo quadro do apêndice caiu de 14 para oito linhas de base. O quadro começa na página 25 e a quebra natural da tabela repete o título e o cabeçalho na página 26, que também contém o terceiro quadro e a subseção final. A mudança preserva o conteúdo, as margens, as fontes, o espaçamento do texto e os créditos dos quadros. Troquei ainda a referência que gerava «A quadro 3» pela forma neutra «Quadro 3». Inspecionei em miniaturas as 74 páginas, com renderizações ampliadas das páginas 25 e 26 da edição ABNT.

| Edição | Primeira validação | Validação final | Links internos resolvidos | SHA-256 final |
|---|---:|---:|---:|---|
| [Original em português](conjecturas_lp.pdf) | 24 | 24 | 245 | `cffdc4feb987f3513a6608cb3e5037a83c749c969aa9c6583eaeade62eeb3c6c` |
| [ABNT](conjecturas_lp_abnt.pdf) | 27 | 26 | 247 | `85079e1755bca847a8361261763dc57491c2559062bc7a967f5e310caf427831` |
| [Inglês](conjecturas_lp_en.pdf) | 24 | 24 | 248 | `f27f491c447d89316cd01c3569cd284453c8071362ac9167df4d6c43294a51a5` |

Os arquivos `.fls` confirmaram as respectivas entradas principais e o uso de `conjecturas_lp_estilo.sty`, `conjecturas_lp_citacoes.tex` e `conjecturas_lp_referencias.tex`. A edição ABNT também lê `conjecturas_lp.tex`. Duas rodadas limpas no mesmo caminho de saída, com data de compilação fixada, produziram PDFs idênticos byte a byte. Uma terceira rodada limpa, em caminho distinto, diferiu apenas no identificador `/ID` do PDF. Os três arquivos versionados foram copiados das saídas verificadas e cada cópia passou em `cmp`.

Cada edição tem 19 chaves bibliográficas únicas, todas usadas, com 23 usos de chaves no TeX. A conferência confirmou a correspondência entre `\abntentry` e `\abntref`, os alvos de todas as citações e referências cruzadas e os 12 URLs de DOI ou preprint definidos no fonte. A extração de texto dos três PDFs confirmou o conteúdo bibliográfico integrado, incluindo o ano 2020 de Kolomoitsev–Tikhonov e os registros de DeVore–Popov (1988b), Petrushev–Popov (1987) e Kerkyacharian–Picard (2003).

A primeira validação conferiu os dados bibliográficos do merge nos registros abaixo. A consulta direta ao site da AMS retornou HTTP 403 naquela etapa. Os metadados do artigo foram conferidos no registro depositado pela AMS no Crossref.

- Kerkyacharian e Picard (2003). Autoria, título, volume, páginas 239–250 e DOI. [Artigo original](https://www.numdam.org/item/10.1051/ps%3A2003011.pdf)
- DeVore e Popov (1988a e 1988b). O capítulo (pp. 191–205) e o artigo (vol. 305, n.º 1, pp. 397–414) são obras distintas. [Capítulo na Springer](https://link.springer.com/chapter/10.1007/BFb0078875) · [Registro da AMS no Crossref](https://api.crossref.org/works/10.1090/s0002-9947-1988-0920166-3)
- Petrushev e Popov (1987). A primeira edição é de 1987 e integra o volume 28 da série da Cambridge. [Exemplar da Cambridge preservado pela ETH](https://people.math.ethz.ch/~hiptmair/Seminars/RAP_22/PEP87.pdf) · [Ficha da editora](https://www.cambridge.org/core/books/rational-approximation-of-real-functions/E81DE7487705CC0623FFD4C51265AB89)
- Kolomoitsev e Tikhonov (2020). DOI, ano, periódico e vínculo com o preprint. [Editora](https://www.sciencedirect.com/science/article/pii/S0021904520300599) · [Preprint](https://arxiv.org/abs/1907.12788)

## Mapa LaTeX–Lean

Regerei o [mapa](mapas/MAPA_TEX_LEAN.md) a partir do JSON. Mantive as 52 entradas e seus estados, os 49 rótulos TeX distintos e as 252 referências a 244 declarações Lean distintas. A comparação estrutural do JSON com o merge passou, descontada a correção da nota do Teorema 3.2. A nota agora atribui `s<1/p` a `conj2_low` e `s=1/p` a `conj2_diag`, em `Formalizacao/LowTheorems.lean`. Cada um dos 49 rótulos aparece uma vez em cada fonte completa. A ABNT compartilha o conjunto da fonte em português.

Os estados são 40 entradas formalizadas e compiladas, seis definições, três reduções condicionais a `J_p`, uma entrada sob `0<q<∞` e duas observações sem declaração própria. Os Teoremas 3.1 a 3.3 mantêm as correspondências nos três regimes de `s` em relação a `1/p`. A seção 6 mantém as correspondências para cotas uniformes, pisos, altura necessária, bits do código explícito e agendas de log iterado. As reduções recebem a estimativa de Jackson como premissa, e os teoremas finais usam sua prova no regime correspondente.

`gerar_mapa.py --verificar` confirmou o Markdown regenerado. `verificar_mapa.py` localizou os alvos nos arquivos e o Lean aceitou os 244 nomes distintos com `#check`.

Os 244 `#print axioms` reproduziram a saída da primeira validação byte a byte. Em 243 nomes aparecem `propext`, `Classical.choice` e `Quot.sound`. Em `Artigo.LTree` aparecem `propext` e `Quot.sound`. A união com a auditoria versionada cobre 264 declarações distintas, com 176 em comum.

## Pendências técnicas e editoriais

- Os avisos do Lean são anteriores à correção de configuração. O trabalho de manutenção de depreciações e de linter pode ser acompanhado pelos logs. O README agora indica as 201 linhas da saída esperada de `Formalizacao/Auditoria.lean`.
- A edição ABNT ainda aguarda os dados oficiais de contato, submissão e aprovação. A palavra «reciprocial» no texto da demonstração e os campos de volume e número de artigo na entrada de Kolomoitsev–Tikhonov continuam como pontos de revisão editorial.

## Questões matemáticas em aberto

- **Entropia métrica (Observação 6.10).** O expoente `1/s` decorre da especialização `d=1` e `π=p` do Teorema 1 de Birman–Solomyak na prova de Kerkyacharian–Picard. A equivalência das quase-normas utilizadas, a aplicação a `[0,1]` e a passagem da cobertura à cota de bits para qualquer codificação ficam fora da verificação do kernel. O corolário sobre o código explícito cobre a cota superior de `O(N log N)` para raio fixo. A cota inferior de ordem `N` para qualquer codificação usa a estimativa externa. O módulo `RequestProject.Entropy` trata de uma classe diferente em distância uniforme. [Teorema 1 no artigo original](https://www.numdam.org/item/10.1051/ps%3A2003011.pdf)
- **Altura aritmética.** Os pisos para a taxa uniforme por escala na bola exigem altura pelo menos da ordem de `N^(1+1/p−s)` abaixo da diagonal, `N` de `s=1/p` a `s=1` e `N^s` acima de `s=1`. A altura linear crítica cobre `p>1`, `0<q<∞` e uma agenda dependente do raio. Ficam em aberto a agenda linear crítica para `q=∞` com `p>1`, a igualdade global com agenda linear para `p>1` e `1<q<∞` e a altura necessária para um alvo fixo. A necessidade dos fatores logarítmicos para a taxa por escala e para a somabilidade são questões distintas e seguem em aberto nos regimes indicados no texto.
- **Fidelidade matemática.** O mapa e a auditoria axiomática verificam a cobertura declarada e as dependências do código. A comparação semântica de ponta a ponta entre as demonstrações em Lean e os enunciados e argumentos das duas línguas continua pendente. O apêndice e a [auditoria de fidelidade](mapas/AUDITORIA_FIDELIDADE.md) registram diferenças de representação, hipóteses e dependência das constantes, em especial em Jackson para `s≤1/p`.

## Comandos e evidências

Da raiz do repositório, para repetir uma rodada de LaTeX com a mesma configuração e verificar os PDFs versionados neste checkout:

```bash
dir=lean4/formalizacao/.lake/validacao-final
mkdir -p "$dir/latex-1"
export SOURCE_DATE_EPOCH="$(git show -s --format=%ct 1601825)" TZ=UTC FORCE_SOURCE_DATE=1
latexmk -pdf -recorder -interaction=nonstopmode -halt-on-error -file-line-error \
  -outdir="$dir/latex-1" conjecturas_lp.tex conjecturas_lp_abnt.tex conjecturas_lp_en.tex
for nome in conjecturas_lp conjecturas_lp_abnt conjecturas_lp_en; do
  qpdf --check "$nome.pdf"
  cmp "$dir/latex-1/$nome.pdf" "$nome.pdf"
done
sha256sum conjecturas_lp*.pdf
```

As rodadas independentes partiram de diretórios de saída vazios. Os logs e os `.fls` ficam na pasta acima, nas subpastas `latex-1`, `latex-1-anterior` e `latex-2`. Usei Poppler (`pdfinfo`, `pdftotext -layout` e `pdftoppm` a 70 e 115 dpi), Pillow e pypdf 6.21.4 para a extração, a inspeção visual e a verificação de destinos.

Com as dependências já instaladas, executei na raiz Lean:

```bash
cd lean4/formalizacao
export LEAN_NUM_THREADS=3 GIT_TERMINAL_PROMPT=0
lake build >.lake/validacao-final/build-padrao.log 2>&1
lake --no-cache build Formalizacao RequestProject Pendencias +Formalizacao.Auditoria \
  >.lake/validacao-final/build-agregados.log 2>&1
sed -nE 's/^info: Formalizacao\/Auditoria\.lean:[0-9]+:[0-9]+: (.*)$/\1/p' \
  .lake/validacao-final/build-agregados.log >.lake/validacao-final/axiomas-build.log
cmp auditoria_axiomas.txt .lake/validacao-final/axiomas-build.log
mapfile -t modules < <(rg --files RequestProject Pendencias -g '*.lean' | sort \
  | sed -e 's/\.lean$//' -e 's|/|.|g' -e 's/^/+/')
test "${#modules[@]}" -eq 85
lake --no-cache build "${modules[@]}" >.lake/validacao-final/build-85.log 2>&1

for fonte in Formalizacao Formalizacao.lean RequestProject Pendencias; do
  /home/victor/.codex/plugins/cache/lean4-skills/lean4/4.12.0/bin/lean4-skills-sorry-analyzer \
    "$fonte" --format=summary
done
lake env lean .lake/validacao-final/AxiomasMapa.lean \
  >.lake/validacao-final/axiomas-mapa-independente.log 2>&1
cmp .lake/validacao-axiomas-mapa.log .lake/validacao-final/axiomas-mapa-independente.log
lake env lean .lake/validacao-final/AxiomasProjeto.lean

cd ../..
python3 mapas/gerar_mapa.py
python3 mapas/gerar_mapa.py --verificar
python3 mapas/verificar_mapa.py
git diff --check 1601825
git diff --exit-code 1601825 -- 'lean4/formalizacao/*.lean' \
  lean4/formalizacao/lean-toolchain lean4/formalizacao/lake-manifest.json
```

Gerei `AxiomasMapa.lean` com as cinco importações de `verificar_mapa.py` e um `#print axioms` por nome distinto de `mapas/dados/mapa_lp.json`, na ordem da primeira ocorrência. `AxiomasProjeto.lean` importa os 162 módulos rastreados e agrupa as constantes pelo módulo de origem informado pelo ambiente do Lean. A pasta local ignorada `lean4/formalizacao/.lake/validacao-final/` conserva o relatório anterior e a evidência bruta desta etapa.
