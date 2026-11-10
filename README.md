# An uncomputable phase diagram at positive temperature for one classical lattice model

Seth Douglas and Nidhal Mghirbi. Version 1.0.0, November 2026. The version 1.0.0 DOI is recorded in the commit that follows the release.

**This is a preprint. It has not been peer reviewed.**

## Abstract

Can the phase diagram of one fixed classical lattice model be uncomputable? For quantum spin systems at zero temperature it can: there are families of Hamiltonians whose spectral gap or ground-state phase cannot be computed from the parameter. We prove a classical counterpart at positive temperature. There is one translation-invariant nearest-neighbour interaction on ℤ², with local energies 0, 1 and +∞ (hard constraints) and a fixed universal Turing machine U built in, and there are disjoint intervals J_n with rational endpoints computable from n, such that at every inverse temperature β in J_n the model has exactly one translation-invariant Gibbs measure if U does not halt on input n, and at least two if U halts. So uniqueness of the translation-invariant Gibbs measure at rational inverse temperature is undecidable for this single model. Uniqueness among all Gibbs measures fails at every temperature, because the hard constraints freeze a non-periodic background.

The background is a hierarchical tiling that contains arbitrarily large square grids. On each grid a Turing machine reads a label n from the size of the grid and runs U on n. Where U halts, small sensors made of free bits and unit energies couple the corner spins of all grids of that size into an ordinary Ising model, whose coupling is large only when β is close to n log 2. Assuming the exact solution of the two-dimensional Ising model, the inverse temperatures with at least two translation-invariant Gibbs measures form exactly a union of explicit intervals around n log 2 over the halting inputs n; restricted to rational β, this set is Σ⁰₁-complete.

## What the paper proves

A lattice model has a finite set of local states at each site of ℤ² and an energy for local patterns. At inverse temperature β its equilibrium states are its Gibbs measures. Its phase diagram records where the Gibbs measure is unique and where phases coexist.

- **Theorem A.** One fixed interaction Φ on ℤ², nearest-neighbour and translation invariant, with every local energy in {0, 1, +∞} and a universal machine U hard-coded. Put λ_K = 2 Σ_{j<K} 1/((2j+1)3^(2j+1)), β_n = n λ_{n+3} and J_n = (β_n − 1/1000, β_n + 1/1000). For every real β in J_n:
  - if U does not halt on n, βΦ has exactly one translation-invariant Gibbs measure;
  - if U halts on n, βΦ has at least two.

  Uniqueness is among translation-invariant Gibbs measures: at every β there are also Gibbs measures that are not translation invariant.
- **Corollary B.** Uniqueness of the translation-invariant Gibbs measure at rational β is undecidable for this one model; the computable rationals β_n carry the halting problem.
- **The exact diagram (conditional).** Assuming the classical exact facts about the two-dimensional Ising model, the coexistence set is exactly the union over halting inputs n of (n log 2 − Δ, n log 2 + Δ), with Δ = (1/20) arcosh(8√2 − 1/64); on rational β it is Σ⁰₁-complete.

The interaction is written out completely in the paper: every field, every local constraint and every energy term (Section 4 and Appendices B and C). The model is a classical, positive-temperature counterpart of the uncomputable quantum phase diagrams of Cubitt, Perez-Garcia and Wolf and of Bausch, Cubitt and Watson. It has hard constraints, and the finite-energy version is the first open problem in the paper.

The proofs build on prior work that the paper credits in detail:
- Wang tiles, and the hierarchical method of Berger and Robinson;
- Ollinger's two-by-two substitution, in the transcription of the lean-wang project, with the ruler decoration of our preprint on forgetting under noise;
- substitution tilings with local rules and unique derivation (Mozes, Mossé, Solomyak);
- the Peierls argument and Dobrushin's uniqueness theorem; for the conditional exact diagram, Onsager, Yang, Aizenman, Higuchi, and Beffara and Duminil-Copin.

Related work credited in the paper includes Kurdyumov and Toom (undecidable ergodicity of probabilistic cellular automata), Gu, Weedbrook, Perales and Nielsen and Gayral, Sablik and Taati (who anticipated undecidable thermodynamics), Miękisz and Taati, Marsan, Sablik and Törmä, and our preprint "Forgetting under noise is undecidable" ([10.5281/zenodo.24105227](https://doi.org/10.5281/zenodo.24105227)).

## Contents and reproduction

- `paper/main.pdf`: manuscript (43 pages).
- `paper/`: LaTeX source (`main.tex`, `preamble-core.tex`, `sections/`), plain-text abstract and a strict build driver. Run `python -B build.py` there with pdflatex installed. The build disables shell escape, runs pdflatex three times and rejects warnings, unresolved references and box defects.

No proof uses a computation.

## Citation and rights

See `CITATION.cff` for citation metadata.
Paper and documentation: CC BY 4.0. The build script: MIT or Apache 2.0, at your option. See `RIGHTS.md`, the license files and `NOTICE`.
