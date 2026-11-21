"""Verificações de integridade compartilhadas pelas edições do artigo."""

import re
import unittest
from collections import Counter
from pathlib import Path


RAIZ = Path(__file__).resolve().parents[1]
PT = (RAIZ / "conjecturas_lp.tex").read_text(encoding="utf-8")
EN = (RAIZ / "conjecturas_lp_en.tex").read_text(encoding="utf-8")
ABNT = (RAIZ / "conjecturas_lp_abnt.tex").read_text(encoding="utf-8")
ROTULO = re.compile(r"\\label\{([^}]+)\}|\\begin\{leantable\}\{[^{}]+\}\{([^}]+)\}")
REFERENCIA = re.compile(r"\\(?:[cC]ref|eqref|ref|pageref)\{([^}]+)\}")
CITACAO = re.compile(r"\\cite[pt](?:\[[^\]]*\])?\{([^}]+)\}")
FORMULA = re.compile(r"\\\[(.*?)\\\]|\\begin\{equation\}(.*?)\\end\{equation\}", re.S)
BLOCOS = (
    ("proposicao", "lp:prop:geom-floor"),
    ("teorema", "lp:thm:critical-linear"),
    ("lema", "lp:lem:nodal-variable-height"),
    ("proposicao", "lp:prop:l1-linear-height"),
    ("lema", "lp:lem:leaf-budget-floor"),
    ("teorema", "lp:thm:minimax-nh"),
    ("corolario", "lp:cor:minimax-realization"),
    ("teorema", "lp:thm:critical-fixed-agenda"),
    ("proposicao", "lp:prop:critical-radius-growth"),
)


def rotulos(fonte):
    return [label or tabela for label, tabela in ROTULO.findall(fonte)]


def chaves(padrao, fonte):
    return {chave.strip() for grupo in padrao.findall(fonte) for chave in grupo.split(",")}


def formulas_com_prova(fonte, ambiente, rotulo):
    inicio = fonte.index(r"\label{" + rotulo + "}")
    fim_enunciado = fonte.index(r"\end{" + ambiente + "}", inicio)
    fim_prova = fonte.index(r"\end{proof}", fim_enunciado)
    return [
        re.sub(r"\s+", "", formula or equacao)
        for formula, equacao in FORMULA.findall(fonte[inicio:fim_prova])
    ]


class EdicoesTest(unittest.TestCase):
    def test_rotulos_unicos_e_na_mesma_ordem(self):
        pt, en = rotulos(PT), rotulos(EN)
        for fonte in (pt, en):
            self.assertEqual([r for r, qtd in Counter(fonte).items() if qtd > 1], [])
        self.assertListEqual(pt, en)

    def test_referencias_e_citacoes_resolvidas(self):
        citacoes = (RAIZ / "conjecturas_lp_citacoes.tex").read_text(encoding="utf-8")
        bibliografia = (RAIZ / "conjecturas_lp_referencias.tex").read_text(encoding="utf-8")
        entradas = set(re.findall(r"\\abntentry\{([^}]+)\}", citacoes))
        destinos = set(re.findall(r"\\abntref\{([^}]+)\}", bibliografia))
        for fonte in (PT, EN):
            self.assertLessEqual(chaves(REFERENCIA, fonte), set(rotulos(fonte)))
            self.assertLessEqual(chaves(CITACAO, fonte), entradas & destinos)
        self.assertEqual(chaves(CITACAO, PT), chaves(CITACAO, EN))

    def test_formulas_dos_novos_resultados(self):
        for ambiente, rotulo in BLOCOS:
            with self.subTest(rotulo=rotulo):
                formulacao = formulas_com_prova(PT, ambiente, rotulo)
                self.assertTrue(formulacao)
                self.assertListEqual(formulacao, formulas_com_prova(EN, ambiente, rotulo))

    def test_abnt_compartilha_a_fonte_portuguesa(self):
        self.assertIn(r"\PassOptionsToPackage{abnt}{conjecturas_lp_estilo}", ABNT)
        self.assertEqual(re.findall(r"\\input\{([^}]+)\}", ABNT), ["conjecturas_lp.tex"])
        self.assertEqual(rotulos(ABNT), [])


if __name__ == "__main__":
    unittest.main()
