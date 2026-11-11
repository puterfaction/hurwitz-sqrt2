# An N^(√2+o(1)) bound for Hurwitz's problem, written out in terms of bilinear forms

**[note.pdf](note.pdf)** (8 pages; source [note.tex](note.tex), Markdown copy [note.md](note.md)) · Lindsay Debnath · November 2026

For every N there are integer bilinear forms f_k, g_k in x_1..x_N, y_1..y_N with

    h! (x_1² + … + x_N²)(y_1² + … + y_N²) = f_1 g_1 + … + f_K g_K,   K = N^(√2+o(1)),

so the bilinear-product variant of Hurwitz's sum-of-squares problem, and σ_C(N), are at most N^(√2+o(1)) (previously N^(1.6147+o(1)), Hrubeš 2024).

The construction is Theorem B of *A 2^o(n) time algorithm for 3-SAT* (Claude / Anthropic, Oct 2026); that it gives this bound was first published by J. P. Siemaszko (7 Nov 2026, [DOI 10.5281/zenodo.24024689](https://doi.org/10.5281/zenodo.24024689)). This note restates the construction directly as an identity of bilinear forms, with explicit coefficients, writes out the proofs of the two lemmas it rests on, and says exactly what is machine-checked. Nothing here is new mathematics beyond the 3-SAT paper.

## What is checked

- **Lean.** Theorem B is formalized in [anthropics/formal-math](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth) (commit `16a5ce41`). [`lean/HurwitzStatement.lean`](lean/HurwitzStatement.lean) states the bound over ℚ for N = 2^λ in terms of polynomials (Mathlib only, about 25 lines of definitions). [`lean/HurwitzProof.lean`](lean/HurwitzProof.lean) proves it from Theorem B. Both rest only on Lean's standard axioms ([`lean/axioms.txt`](lean/axioms.txt)).
- **Numerics.** [`checks/check_lemmas.py`](checks/check_lemmas.py) (exact integer arithmetic, written from the paper's text) checks both lemmas, the crossing identity and the multiplied-out polynomial identity for small cases; output in [`checks/check_lemmas.out`](checks/check_lemmas.out).

## Reproducing

```sh
git clone https://github.com/anthropics/formal-math && cd formal-math && git checkout 16a5ce41304fcdaea4e0be7c132e1c361dc26da5 && cd eth
lake exe cache get
lake build GeneralPieces.Main
lake env lean /path/to/this/repo/lean/ThmB.lean
lake env lean /path/to/this/repo/lean/HurwitzProof.lean   # prints the axioms of hurwitzSqrt2
python3 /path/to/this/repo/checks/check_lemmas.py          # about 3 minutes
```

## Provenance

The note, the Lean bridge and the scripts were produced with Claude models (Anthropic) in sessions directed by the author, who has not verified the mathematics independently of the checks described. Corrections are welcome as issues.

## License

Text (note.*, README): CC BY 4.0. Code (lean/, checks/): MIT.
