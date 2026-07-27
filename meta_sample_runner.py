#!/usr/bin/env python3
"""Run samples through the evaluator structure used by miniml3 meta.mml.

This mirrors the prefix-code evaluator in meta.mml:
node = (tag, name, number)
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


Node = tuple[str, str, int]
Code = list[Node]
Env = list[tuple[str, int]]
Def = tuple[list[str], Code]
Defs = list[tuple[str, Def]]


def num(k: int) -> Node:
    return ("n", "", k)


def var(x: str) -> Node:
    return ("v", x, 0)


def op(g: str) -> Node:
    return (g, "", 0)


def call(f: str, k: int) -> Node:
    return ("call", f, k)


IF: Node = ("if", "", 0)
NEG: Node = ("~", "", 0)


def arity(t: Node) -> int:
    g, _, n = t
    if g in {"n", "v"}:
        return 0
    if g == "~":
        return 1
    if g == "let":
        return 2
    if g == "if":
        return 3
    if g == "call":
        return n
    return 2


def skipn(k: int, code: Code) -> Code:
    i = 0
    rest = code
    while k != 0 and rest:
        t, rest = rest[0], rest[1:]
        k = k - 1 + arity(t)
    return rest


def skip1(code: Code) -> Code:
    return skipn(1, code)


def look(x: str, env: Env) -> int:
    for name, value in env:
        if name == x:
            return value
    return 0


def findf(f: str, defs: Defs) -> Def:
    for name, definition in defs:
        if name == f:
            return definition
    return ([], [])


def bind(params: list[str], values: list[int]) -> Env:
    return list(zip(params, values))


def binop(g: str, a: int, b: int) -> int:
    if g == "+":
        return a + b
    if g == "-":
        return a - b
    if g == "*":
        return a * b
    if g == "/":
        return a // b
    if g == "%":
        # meta.mml's "%" is MiniML's mod, which follows OCaml: the remainder
        # takes the sign of the dividend.  Python's % takes the sign of the
        # divisor, so (-7) % 3 is 2 there but -1 here.  Note that "/" stays
        # floor division, matching MiniML's / -- the reference is inconsistent
        # in exactly this way and the mirror has to be too.
        r = abs(a) % abs(b)
        return r if a >= 0 else -r
    if g == "<":
        return int(a < b)
    if g == ">":
        return int(a > b)
    if g == "<=":
        return int(a <= b)
    if g == ">=":
        return int(a >= b)
    if g == "=":
        return int(a == b)
    if g == "#":
        return int(a != b)
    if g == "&":
        return int(a != 0 and b != 0)
    if g == "|":
        return int(a != 0 or b != 0)
    return 0


def evargs(k: int, code: Code, env: Env, defs: Defs) -> tuple[list[int], Code]:
    values: list[int] = []
    rest = code
    for _ in range(k):
        value, rest = ev(rest, env, defs)
        values.append(value)
    return values, rest


def ev(code: Code, env: Env, defs: Defs) -> tuple[int, Code]:
    if not code:
        return 0, []

    t, r = code[0], code[1:]
    g, name, n = t

    if g == "n":
        return n, r
    if g == "v":
        return look(name, env), r
    if g == "~":
        a, rest = ev(r, env, defs)
        return -a, rest
    if g == "if":
        c, after_c = ev(r, env, defs)
        if c != 0:
            a, after_a = ev(after_c, env, defs)
            return a, skip1(after_a)
        b, after_b = ev(skip1(after_c), env, defs)
        return b, after_b
    if g == "let":
        a, after_a = ev(r, env, defs)
        b, after_b = ev(after_a, [(name, a), *env], defs)
        return b, after_b
    if g == "call":
        values, rest = evargs(n, r, env, defs)
        params, body = findf(name, defs)
        b, _ = ev(body, bind(params, values), defs)
        return b, rest

    a, after_a = ev(r, env, defs)
    b, after_b = ev(after_a, env, defs)
    return binop(g, a, b), after_b


def run(defs: Defs, code: Code) -> int:
    return ev(code, [], defs)[0]


def unp(code: Code) -> tuple[str, Code]:
    if not code:
        return "", []
    t, r = code[0], code[1:]
    g, name, n = t
    if g == "n":
        return str(n), r
    if g == "v":
        return name, r
    if g == "~":
        a, rest = unp(r)
        return f"(-{a})", rest
    if g == "if":
        c, r1 = unp(r)
        a, r2 = unp(r1)
        b, r3 = unp(r2)
        return f"(if {c} then {a} else {b})", r3
    if g == "let":
        a, r1 = unp(r)
        b, r2 = unp(r1)
        return f"(let {name} = {a} in {b})", r2
    if g == "call":
        parts = []
        rest = r
        for _ in range(n):
            text, rest = unp(rest)
            parts.append(text)
        return f"({name} {' '.join(parts)})", rest
    a, r1 = unp(r)
    b, r2 = unp(r1)
    display = {"%": "mod", "#": "<>", "&": "&&", "|": "||"}.get(g, g)
    return f"({a} {display} {b})", r2


def unparse(code: Code) -> str:
    return unp(code)[0]


def definitions() -> Defs:
    d_fac = (
        "fac",
        (
            ["n"],
            [
                IF,
                op("="), var("n"), num(0),
                num(1),
                op("*"), var("n"), call("fac", 1), op("-"), var("n"), num(1),
            ],
        ),
    )
    d_fib = (
        "fib",
        (
            ["n"],
            [
                IF,
                op("<"), var("n"), num(2),
                var("n"),
                op("+"),
                call("fib", 1), op("-"), var("n"), num(1),
                call("fib", 1), op("-"), var("n"), num(2),
            ],
        ),
    )
    d_gcd = (
        "gcd",
        (
            ["a", "b"],
            [
                IF,
                op("="), var("b"), num(0),
                var("a"),
                call("gcd", 2), var("b"), op("%"), var("a"), var("b"),
            ],
        ),
    )
    d_pow = (
        "pow",
        (
            ["b", "k"],
            [
                IF,
                op("="), var("k"), num(0),
                num(1),
                op("*"), var("b"), call("pow", 2), var("b"), op("-"), var("k"), num(1),
            ],
        ),
    )
    return [d_fac, d_fib, d_gcd, d_pow]


LET: Callable[[str], Node] = lambda x: ("let", x, 0)


def checks() -> None:
    """Pin the places where this mirror could drift from meta.mml.

    The expected values are what ./miniml3 meta.mml actually prints.
    """
    value_cases: list[tuple[str, Code, int]] = [
        ("(-7) mod 3", [op("%"), NEG, num(7), num(3)], -1),
        ("7 mod (-3)", [op("%"), num(7), NEG, num(3)], 1),
        ("(-7) mod (-3)", [op("%"), NEG, num(7), NEG, num(3)], -1),
        ("(-7) / 3", [op("/"), NEG, num(7), num(3)], -3),
        ("let x = 5 in x * x",
         [LET("x"), num(5), op("*"), var("x"), var("x")], 25),
        ("let a = 6 in let b = 7 in a * b",
         [LET("a"), num(6), LET("b"), num(7), op("*"), var("a"), var("b")], 42),
    ]
    text_cases: list[tuple[str, Code, str]] = [
        ("let unparses",
         [LET("x"), num(5), op("*"), var("x"), var("x")],
         "(let x = 5 in (x * x))"),
    ]

    print("-- agreement with meta.mml --")
    bad = 0
    for name, code, want in value_cases:
        got = run([], code)
        bad += got != want
        print(f"  {'OK ' if got == want else 'NG '} {name:24s} = {got}"
              + ("" if got == want else f"  (meta.mml gives {want})"))
    for name, code, want in text_cases:
        got = unparse(code)
        bad += got != want
        print(f"  {'OK ' if got == want else 'NG '} {name:24s} = {got}"
              + ("" if got == want else f"  (meta.mml gives {want})"))
    if bad:
        raise SystemExit(f"{bad} case(s) disagree with meta.mml")


def main() -> None:
    defs = definitions()
    samples: list[tuple[str, Code]] = [
        ("1 + 2 * 3", [op("+"), num(1), op("*"), num(2), num(3)]),
        ("fac 10", [call("fac", 1), num(10)]),
        ("fib 25", [call("fib", 1), num(25)]),
        ("gcd 1071 462", [call("gcd", 2), num(1071), num(462)]),
        ("pow 2 100", [call("pow", 2), num(2), num(100)]),
    ]

    print("-- meta.mml prefix evaluator sample --")
    for name, code in samples:
        print(f"{name:14s}  {unparse(code)}")
        print(f"{'':14s}= {run(defs, code)}")

    facs = [run(defs, [call("fac", 1), num(k)]) for k in range(11)]
    fibs = [run(defs, [call("fib", 1), num(k)]) for k in range(16)]
    print("fac 0..10     =", facs)
    print("fib 0..15     =", fibs)
    print()
    checks()


if __name__ == "__main__":
    main()
