# ARTIGO-BESOV

**Caracterização dos espaços de Besov em $L^p$ por realização com altura aritmética controlada**
Victor Gabriel de Oliveira, 19 de novembro de 2026.

## Sobre o artigo

O artigo caracteriza os espaços de Besov $B^s_{p,q}([0,1])$, com $1\le p<\infty$, $1/p<s<2$ e $0<q\le\infty$, pela somabilidade diádica de um *funcional de realização*. Esse funcional combina o erro em $L^p$ e o módulo de suavidade de segunda ordem do aproximante. O ínfimo é tomado sobre funções contínuas e afins por partes, com coeficientes racionais, definidas em partições diádicas e sujeitas a orçamentos simultâneos de folhas e de altura aritmética.

Resultados principais:

- **Teorema de Jackson racional em $L^p$.** Existe um aproximante com até $n$ folhas e altura $H$, com erro limitado por $C_p\,\omega_2(f,n^{-1})_p + 16(\|f\|_\infty+1)/H$. A prova combina quase-interpolação por projeções afins locais, uma desigualdade de Whitney em partições e quantização dos valores nodais em grades alternadas.
- **Caracterização de Besov.** As agendas de altura são da ordem de $N^{\max\{1,s\}}$ para $q=\infty$ e para $q<\infty$ com $s<1$. Para $q<\infty$ e $s\ge1$ basta um fator logarítmico de expoente $\kappa>1/q$.
- **Estabilidade.** A caracterização vale para toda família aninhada de funções realizadas por redes ReLU que contenha a biblioteca racional após um reescalonamento linear do orçamento.

O apêndice do artigo descreve a formalização em Lean 4 e a correspondência entre as demonstrações e as declarações verificadas.

## Conteúdo do repositório

| Caminho | Descrição |
|---|---|
| `conjecturas_lp.tex` / `conjecturas_lp.pdf` | Fonte e PDF do artigo. |
| `lean4/formalizacao/` | Projeto Lean 4 com a formalização (Lean 4.28.0, Mathlib v4.28.0). |
| `lean4/formalizacao/Formalizacao/` | Módulos principais: módulo de suavidade, Besov, Whitney, quase-interpolação, imersão, Jackson, caracterização e estabilidade. |
| `lean4/formalizacao/Pendencias/`, `RequestProject/` | Módulos auxiliares dos quais `Formalizacao` depende. |
| `lean4/formalizacao/auditoria_axiomas.txt` | Saída da auditoria de axiomas. |
| `mapas/` | Mapa entre rótulos do TeX e nomes Lean (`MAPA_TEX_LEAN.md`), scripts de geração e verificação, e relatório de fidelidade (`AUDITORIA_FIDELIDADE.md`). |

## Como verificar de forma independente

### 1. Compilar o artigo

Requer uma distribuição TeX Live com `pdflatex`, `babel` com suporte a português, `cleveref`, `tgtermes` e `lmodern`.

```bash
pdflatex conjecturas_lp.tex
pdflatex conjecturas_lp.tex
```

São necessárias duas passagens para resolver as referências cruzadas.

### 2. Instalar o Lean

Instale o `elan`, que escolhe o toolchain indicado em `lean4/formalizacao/lean-toolchain` (`leanprover/lean4:v4.28.0`):

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

### 3. Compilar a formalização

O Mathlib é fixado em `v4.28.0` pelo `lake-manifest.json`. Baixar o cache pré-compilado evita horas de compilação:

```bash
cd lean4/formalizacao
lake exe cache get
lake build Formalizacao
```

A compilação deve terminar com `Build completed successfully`. Nenhum `sorry` deve aparecer nos módulos de `Formalizacao`:

```bash
grep -rn "sorry" Formalizacao/ Formalizacao.lean
```

(A única ocorrência esperada é uma menção em comentário em `Formalizacao/Auditoria.lean`.)

### 4. Auditar os axiomas

```bash
lake env lean Formalizacao/Auditoria.lean
```

A saída deve ter 108 linhas, todas com `depends on axioms: [propext, Classical.choice, Quot.sound]`, e nenhuma com `sorryAx`. A saída de referência está em `auditoria_axiomas.txt`. Conferência rápida:

```bash
lake env lean Formalizacao/Auditoria.lean | grep -vc "\[propext, Classical.choice, Quot.sound\]"
```

O resultado esperado é `0`.

### 5. Conferir a correspondência TeX–Lean

Na raiz do repositório:

```bash
python3 mapas/verificar_mapa.py
```

O script confere que os rótulos do TeX e os nomes Lean listados em `mapas/MAPA_TEX_LEAN.md` existem e são aceitos pelo Lean (`#check`). Requer Python 3 e o projeto Lean já compilado.

## Observações sobre o escopo da formalização

- Os enunciados Lean tratam funções mensuráveis $\mathbb R\to\mathbb R$ com a medida de Lebesgue restrita a $[0,1]$, em vez de classes de $L^p$. Os casos com agenda $\widetilde H_{s,\eta}$ são enunciados com $1/p<s<2$, como no artigo.
- As reduções usam a forma do teorema de Jackson com constantes que podem depender de $f$. A forma com constantes explícitas ($C_0=9C_W(p)$, $C_1=16$) está em `hypJpStrong_of_lt`.
- O relatório `mapas/AUDITORIA_FIDELIDADE.md` compara, item a item, o texto do artigo com os enunciados Lean.
