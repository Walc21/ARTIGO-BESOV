"""Verificação exata da construção de lp:lem:nodal-variable-height."""

import unittest
from fractions import Fraction
from random import Random


def parametros(dados):
    n = len(dados) - 1
    salto = max(abs(b - a) for a, b in zip(dados, dados[1:]))
    pesos = [1 + salto + abs(valor) for valor in dados]
    return salto, pesos, max(8 * max(pesos), n * (salto + 4))


def quantizar(dados, altura):
    _, pesos, limiar = parametros(dados)
    if altura < limiar:
        raise ValueError("altura inferior ao limiar do lema")
    denominadores = [
        1 << (int(altura / (8 * peso)).bit_length() - 1) for peso in pesos
    ]
    proximos = [
        round(q * valor) for q, valor in zip(denominadores, dados)
    ]
    valores = [
        Fraction(numerador, q) for numerador, q in zip(proximos, denominadores)
    ]
    for j in range(1, len(dados) - 1, 2):
        proibidos = {valores[j - 1], valores[j + 1]}
        for desvio in (0, -1, 1):
            candidato = Fraction(proximos[j] + desvio, denominadores[j])
            if candidato not in proibidos:
                valores[j] = candidato
                break
    return denominadores, valores


def altura_racional(valor):
    return max(abs(valor.numerator), valor.denominator)


def integral_modulo_afim(a, b, n):
    """Integra o módulo de uma reta com extremos a, b em comprimento 1/n."""
    if a * b >= 0:
        return (abs(a) + abs(b)) / (2 * n)
    return (a**2 + b**2) / (2 * n * (abs(a) + abs(b)))


class QuantizacaoVariavelTest(unittest.TestCase):
    def verificar(self, dados, altura):
        n = len(dados) - 1
        r = n.bit_length() - 1
        salto, pesos, _ = parametros(dados)
        denominadores, valores = quantizar(dados, altura)
        erros = [v - y for v, y in zip(valores, dados)]
        for erro, q, w in zip(erros, denominadores, pesos):
            self.assertGreater(q, 0)
            self.assertEqual(q & (q - 1), 0)
            self.assertLessEqual(8 * w * q, altura)
            self.assertGreater(16 * w * q, altura)
            self.assertLessEqual(abs(erro), Fraction(2, q))
            self.assertLessEqual(abs(erro), 32 * w / altura)

        integral = 0
        extremo_anterior = None
        comparacoes = set()
        mudou_denominador = False
        for j, (esquerdo, direito) in enumerate(zip(valores, valores[1:])):
            qa, qb = denominadores[j:j + 2]
            d = max(qa, qb)
            mudou_denominador |= qa != qb
            comparacoes.add((d > n) - (d < n))
            self.assertEqual(d % qa, 0)
            self.assertEqual(d % qb, 0)
            self.assertLessEqual(8 * min(pesos[j:j + 2]) * d, altura)
            self.assertEqual((esquerdo * d).denominator, 1)
            self.assertEqual((direito * d).denominator, 1)

            centro = (esquerdo + direito) / 2
            inclinacao = n * (direito - esquerdo)
            self.assertNotEqual(inclinacao, 0)
            if d < n:
                self.assertEqual(inclinacao.denominator, 1)
                self.assertLessEqual(abs(inclinacao), n * (salto + 4))

            altura_folha = max(
                2, r + 1, j + 1, altura_racional(centro), altura_racional(inclinacao)
            )
            self.assertLessEqual(altura_folha, altura)
            meio_passo = Fraction(1, 2 * n)
            extremo_esquerdo = centro - inclinacao * meio_passo
            extremo_direito = centro + inclinacao * meio_passo
            self.assertEqual(extremo_esquerdo, esquerdo)
            self.assertEqual(extremo_direito, direito)
            if extremo_anterior is not None:
                self.assertEqual(extremo_esquerdo, extremo_anterior)
            extremo_anterior = extremo_direito
            integral += integral_modulo_afim(erros[j], erros[j + 1], n)

        self.assertLessEqual(integral, sum(map(abs, erros)) / n)
        self.assertLessEqual(integral, 32 * sum(pesos) / (altura * n))
        return comparacoes, mudou_denominador

    def test_casos_adversariais(self):
        casos = [
            ("constante mínima", [0, 0, 0], 8),
            ("constante negativa", [-3, -3, -3], 64),
            ("quase constante", [Fraction(3, 2) + Fraction(j, 10**9) for j in range(9)], None),
            ("duas proibições", [0, Fraction(1, 4), 1], 24),
            ("sinais e amplitudes", [0, -1000, 1000, Fraction(-1, 8), 0], None),
            ("mudança de grade", [0, 200, 0], 3216),
            ("igualdade D=n", [0, 0, 0], 16),
            ("D maior que n", [0, 0, 0], 32),
            ("limiar de inclinação", [0] * 9, 32),
        ]
        regimes = set()
        mudanca = False
        for nome, dados, altura in casos:
            with self.subTest(nome=nome):
                dados = list(map(Fraction, dados))
                _, _, limiar = parametros(dados)
                altura = altura if altura is not None else limiar.__ceil__()
                comparacoes, mudou = self.verificar(dados, altura)
                regimes |= comparacoes
                mudanca |= mudou
        self.assertEqual(regimes, {-1, 0, 1})
        self.assertTrue(mudanca)

    def test_altura_abaixo_do_limiar(self):
        with self.assertRaises(ValueError):
            quantizar([Fraction(0)] * 9, 31)

    def test_amostra_reproduzivel(self):
        rng = Random(63)
        for n in (2, 4, 8, 16, 64, 256):
            for caso in range(100):
                with self.subTest(n=n, caso=caso):
                    dados = [
                        Fraction(rng.randrange(-8192, 8193), 2 ** rng.randrange(1, 13))
                        for _ in range(n + 1)
                    ]
                    _, _, limiar = parametros(dados)
                    altura = limiar.__ceil__() * rng.choice((1, 2, 16, 256))
                    self.verificar(dados, altura)


if __name__ == "__main__":
    unittest.main()
