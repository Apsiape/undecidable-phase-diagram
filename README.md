# An uncomputable phase diagram at positive temperature for one classical lattice model

Seth Douglas and Nidhal Mghirbi. Version 1.2.0, November 2026. DOI: [10.5281/zenodo.24144192](https://doi.org/10.5281/zenodo.24144192). Version 1.1.0: [10.5281/zenodo.24124685](https://doi.org/10.5281/zenodo.24124685). Version 1.0.0: [10.5281/zenodo.24115745](https://doi.org/10.5281/zenodo.24115745). Concept DOI (all versions): [10.5281/zenodo.24115744](https://doi.org/10.5281/zenodo.24115744).

**This is a preprint. It has not been peer reviewed.**

## Abstract

Can the phase diagram of one fixed classical lattice model be uncomputable? For quantum spin systems at zero temperature it can: there are families of Hamiltonians whose spectral gap or ground-state phase cannot be computed from the parameter. We prove a classical counterpart at positive temperature. There is one translation-invariant nearest-neighbour interaction on ℤ², with local energies 0, 1 and +∞ (hard constraints) and a fixed universal Turing machine U built in, and there are disjoint intervals J_n with rational endpoints computable from n, such that at every inverse temperature β in J_n the model has exactly one translation-invariant Gibbs measure if U does not halt on input n, and at least two if U halts. So uniqueness of the translation-invariant Gibbs measure at rational inverse temperature is undecidable for this single model. Uniqueness among all Gibbs measures fails at every temperature, because the hard constraints freeze a non-periodic background. These results are proved in Lean, with Dobrushin's uniqueness theorem and the existence of the plus state of the two-dimensional Ising model taken as hypotheses.

The background is a hierarchical tiling that contains arbitrarily large square grids. On each grid a Turing machine reads a label n from the size of the grid and runs U on n. Where U halts, small sensors made of free bits and unit energies couple the corner spins of all grids of that size into an ordinary Ising model, whose coupling is large only when β is close to n log 2. Assuming the exact solution of the two-dimensional Ising model, the inverse temperatures with at least two translation-invariant Gibbs measures form exactly a union of explicit intervals around n log 2 over the halting inputs n; restricted to rational β, this set is Σ⁰₁-complete.

## What the paper proves

A lattice model has a finite set of local states at each site of ℤ² and an energy for local patterns. At inverse temperature β its equilibrium states are its Gibbs measures. Its phase diagram records where the Gibbs measure is unique and where phases coexist.

- **Theorem A.** One fixed interaction Φ on ℤ², nearest-neighbour and translation invariant, with every local energy in {0, 1, +∞} and a universal machine U hard-coded. Put λ_K = 2 Σ_{j<K} 1/((2j+1)3^(2j+1)), β_n = n λ_{n+3} and J_n = (β_n − 1/1000, β_n + 1/1000). For every real β in J_n:
  - if U does not halt on n, βΦ has exactly one translation-invariant Gibbs measure;
  - if U halts on n, βΦ has at least two.

  Uniqueness is among translation-invariant Gibbs measures: at every β there are also Gibbs measures that are not translation invariant.
- **Corollary B.** Uniqueness of the translation-invariant Gibbs measure at rational β is undecidable for this one model; the computable rationals β_n carry the halting problem.
- **The exact diagram (conditional).** Assuming the classical exact facts about the two-dimensional Ising model, the coexistence set is exactly the union over halting inputs n of (n log 2 − Δ, n log 2 + Δ), with Δ = (1/20) arcosh(8√2 − 1/64); on rational β it is Σ⁰₁-complete.
- **Formal proof (version 1.2.0).** Theorem A, Corollary B and the existence of a universal machine U are proved in Lean 4 with Mathlib (Appendix D). Theorem A and Corollary B are proved from two published results that Mathlib lacks, taken as named hypotheses: Dobrushin's uniqueness theorem and the existence of the plus state of the two-dimensional Ising model, in the form of Friedli and Velenik's book. The sources, the comparator check against a challenge file that imports only Mathlib, two kernel replays and the axiom audit are in `lean/`.

The interaction is written out completely in the paper: every field, every local constraint and every energy term (Section 4 and Appendices B and C). The model is a classical, positive-temperature counterpart of the uncomputable quantum phase diagrams of Cubitt, Perez-Garcia and Wolf and of Bausch, Cubitt and Watson. It has hard constraints, and the finite-energy version is the first open problem in the paper.

The proofs build on prior work that the paper credits in detail:
- Wang tiles, and the hierarchical method of Berger and Robinson;
- Ollinger's two-by-two substitution, in the transcription of the lean-wang project, with the ruler decoration of our preprint on forgetting under noise;
- substitution tilings with local rules and unique derivation (Mozes, Mossé, Solomyak);
- the Peierls argument and Dobrushin's uniqueness theorem; for the conditional exact diagram, Onsager, Yang, Aizenman, Higuchi, and Beffara and Duminil-Copin;
- the proof assistant Lean 4 and its library Mathlib, for the formal proof.

Related work credited in the paper includes Kurdyumov and Toom (undecidable ergodicity of probabilistic cellular automata), Gu, Weedbrook, Perales and Nielsen and Gayral, Sablik and Taati (who anticipated undecidable thermodynamics), Miękisz and Taati, Marsan, Sablik and Törmä, and our preprints "Forgetting under noise is undecidable" ([10.5281/zenodo.24105227](https://doi.org/10.5281/zenodo.24105227)) and "Spontaneous magnetization and thermal decay are undecidable at positive temperature" ([10.5281/zenodo.23962706](https://doi.org/10.5281/zenodo.23962706)).

## Changes in version 1.2.0

Version 1.2.0 adds the formalization in Lean 4 of Theorem A, Corollary B and the existence of the universal machine U (Appendix D and `lean/`). The formal Theorem A and Corollary B take Dobrushin's uniqueness theorem and the existence of the plus state of the two-dimensional Ising model as hypotheses. The formalization found no false step. It found three imprecise sentences, corrected in this version:
- Section 2: the kernel of a specification by factors is now defined where its normalization is 0 (it is 0 there).
- Section 4.7 and the proof of Lemma 6.1: the rules that involve payload coordinates include rule (K2) and the matching of colours.
- Section 6: the sensor coordinates of an edge include the components of ℓ^S and ℓ^N only where these colours are not ∘.

One sentence of the abstract, "How this work was done" and "Verification status" describe the formalization. References to the appendices now print as "Appendix". No other statement or proof has changed.

## Changes in version 1.1.0

Version 1.1.0 adds a citation of the authors' preprint *Spontaneous magnetization and thermal decay are undecidable at positive temperature* (version 1.2.0, DOI [10.5281/zenodo.23962706](https://doi.org/10.5281/zenodo.23962706)), which version 1.0.0 did not cite: two sentences in the prior work of the introduction, a row of Table 1 and one sentence in Section 9. That preprint makes spontaneous magnetization, exponential decay of a specified spin correlation and uniqueness of the Gibbs measure undecidable at one fixed positive temperature, for computable families of interactions on ℤ² with strictly positive rational Boltzmann weights, in which the interaction and its range depend on the input. Theorem A instead fixes one nearest-neighbour interaction, with hard constraints, carries the input in the inverse temperature, and makes undecidable uniqueness among translation-invariant Gibbs measures. No statement or proof has changed.

## Contents and reproduction

- `paper/main.pdf`: manuscript (47 pages).
- `lean/`: the formal proof in Lean 4 with Mathlib of Theorem A, Corollary B and the existence of a universal machine, described in Appendix D of the paper ([release v1.2.0](https://github.com/Apsiape/undecidable-phase-diagram/tree/v1.2.0/lean)). It holds the sources, the pins, the named hypotheses (`UndecidablePhaseDiagram/Hypotheses.lean`), the comparator challenge (`Challenge.lean`, which imports only Mathlib), and the records of the sandboxed comparator run, of the replays of the proof by the kernel checkers leanchecker and nanoda, and of the axiom audit. Start with `lean/README.md`.
- `paper/`: LaTeX source (`main.tex`, `preamble-core.tex`, `sections/`), plain-text abstract and a strict build driver. Run `python -B build.py` there with pdflatex installed. The build disables shell escape, runs pdflatex three times and rejects warnings, unresolved references and box defects.
- `SHA256SUMS`: SHA-256 hashes of every shipped file except this manifest. Check with `sha256sum -c SHA256SUMS` from the repository root.

No proof in the text uses a computation.

## Citation and rights

See `CITATION.cff` for citation metadata.
Paper, documentation and recorded outputs: CC BY 4.0. The build script and the Lean sources and scripts in `lean/`: MIT or Apache 2.0, at your option. See `RIGHTS.md`, the license files and `NOTICE`.
