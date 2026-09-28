# Provenance

**Paper.** *What Transport Keeps: Projector selection, conserved pairings, and spectral geometry
after the Ramanujan Challenge*, follow-up research edition 3, 6 September 2026.
Zenodo version DOI [10.5281/zenodo.22543487](https://doi.org/10.5281/zenodo.22543487)
(all versions: [10.5281/zenodo.22543486](https://doi.org/10.5281/zenodo.22543486)).

The Zenodo record's files, with the MD5 checksums the record lists and that the copies used here
match:

```
532da23c5edf658632b886381a31eb17  What_Transport_Keeps (3).html
0ac3fdb8b96d9265994c0ea040bc774a  What_Transport_Keeps_Proofs_and_Code (3).zip
```

**How the Lean files were made.** The four modules in `WTK/` were written for this repository
from the paper's statements and the code package. The polynomial matrices `Tnum`, `Lnum` and
`Mm` in `WTK/Field.lean` were generated from `cmf_explicit.py` in the code package
(MD5 `64470eb63b9a1564fb9a826645f65615`) by clearing the common denominators
`D(n) = 4(n+1)(n+2)(n+3)(2n+3)(2n+5)` and `E(k) = 2(2k-7)`; the column convention, plaquette
identity and determinant factorization were confirmed symbolically before being proved in Lean.
The Bézout certificates for the curvature numerator and denominator are extended-gcd
certificates computed in the same way and checked by Lean's `ring`.

Lean v4.34.1, Mathlib v4.34.1. First verified at commit
`243705017a9227189b54edacb339e0e15755abcd` (GitHub Actions run 36375969258).

## SHA-256

```
2ad3e9b77283a398ab56f17fefb449cdb4d7d027de67e4e28226f968f1f4bd5a  WTK/Transport.lean
e12cc60372de8e39750d6fd231fb38012e32ef8b3f7c6e046caaac1a0fa6e31d  WTK/Catalan.lean
39f0004f937a4bdc917656e26ec77bd971711a5f7c611b092828c38574943bc6  WTK/Field.lean
f3506253b19382a04bceca4653412f347eb000a574af10590ead455a2a3b0c12  WTK/Response.lean
```
