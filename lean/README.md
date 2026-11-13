# Lean formalization: Theorem A and Corollary B

This directory proves Theorem A and Corollary B of the paper, and the existence of a universal machine as in Section 2.2, in Lean 4 with Mathlib. The proofs have no unproved step and use no axioms beyond Lean's three standard axioms `propext`, `Classical.choice` and `Quot.sound`. Theorem A and Corollary B are proved from two published theorems that Mathlib lacks: Dobrushin's uniqueness theorem (`H1`) and the plus state of the two-dimensional Ising model (`H2`). They are explicit hypotheses of the two final theorems, not axioms. Appendix D of the paper describes the formalization.

## Reproduce

Install the toolchain specified by `lean-toolchain` (Lean 4.35.0), and have Git and Mathlib's cache prerequisites available. From this directory run:

```sh
export LEAN_NUM_THREADS=1
lake exe cache get
lake build
lake env lean -j1 -M6144 Audit.lean
```

The cache command fetches the pinned Git dependencies and Mathlib's standard build cache. Plain `lake build` compiles the entire `UndecidablePhaseDiagram` library from the shipped sources. Compare the audit's axiom lines with `AXIOMS.txt`; this paper's recorded hypothesis policy in the evidence and statement files remains authoritative. Named hypotheses are preserved. The standard build does not run the comparator, the custom Python replay, or independent kernel replays, and does not rewrite `AXIOMS.txt`.

Allow at least 8 GiB of available physical memory and run one Lean compiler process on the machine at a time. The package passes `-j1 -M6144`. On PowerShell set `$env:LEAN_NUM_THREADS = '1'`. Compiler thread limits do not provide a machine-wide process lock: serialize launches externally and check memory before building. This toolchain's Lake has no `lake build -j1` option.

Mathlib is required by Git at `56a005855ea17e0b0958f73ec801ae140b0a1679`; the Lake-generated manifest pins its eight inherited dependencies to the recorded revisions. Use the shipped manifest; ordinary reproduction does not require `lake update`. The stock Mathlib cache tool is used without the historical override.

`Challenge.lean`, `Solution.lean`, and `Audit.lean` are ordinary files checked with `lake env lean -j1 -M6144 FILE.lean`. Challenge retains its intentional comparator holes and is excluded from the library. Library and final audit output must have no `declaration uses sorry` warnings.

`UPDStatements` is a separate library with only `UndecidablePhaseDiagram.Statements` as its root. It supplies `-Dbackward.isDefEq.respectTransparency=false` for the unchanged Lean 4.35 `Fintype` derivations. Other modules retain their original elaboration options. The two UPD libraries together cover exactly the original module set (or the consuming package's recorded subset).

The Python replay, evidence, and previous reproduction instructions below are retained as optional historical tools. They assume the old `vendor/` layout, prebuilt objects, and in some cases a host-memory heartbeat; plain `lake build` does not invoke them. Run any historical preparation in a separate copy and retain the standard manifest in this one. Historical checks describe the original release, not new comparator or kernel replays by the standard build.

## What is proved

`UndecidablePhaseDiagram/Statements.lean` defines, with no proofs of substance, every object that occurs in Theorem A and Corollary B: interactions, legal configurations, energies, Gibbs kernels and Gibbs measures (Section 2.1), Turing machines (Section 2.2), the scaffold alphabet (Section 3 and Appendix A), the fields, rules, colours and charge of the interaction (Section 4), the machine M (Appendix C), the interaction Φ (Definition 4.1) and the numbers λ_K, β_n and intervals J_n (Lemma 7.1). Every definition carries a comment naming the label of the paper that it mirrors. The file states Theorem A and Corollary B as propositions:

```lean
def TheoremA : Prop :=
  ∀ U : Machine,
    IsInteraction (Phi U) ∧ IsTranslationInvariant (Phi U) ∧ IsNearestNeighbour (Phi U) ∧
    (∀ (A : Finset Plane) (ω : Config (SiteVal U)),
      Phi U A ω = 0 ∨ Phi U A ω = 1 ∨ Phi U A ω = ⊤) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < (betaN n : ℝ) - 1 / 1000) ∧
    (∀ n m : ℕ, 1 ≤ n → n < m → Disjoint (J n) (J m)) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ β ∈ J n,
      (¬ U.HaltsOn n → ∃! μ : Measure (Config (SiteVal U)), IsTIGibbs U β μ) ∧
      (U.HaltsOn n → ∃ μ₁ μ₂ : Measure (Config (SiteVal U)),
        μ₁ ≠ μ₂ ∧ IsTIGibbs U β μ₁ ∧ IsTIGibbs U β μ₂)) ∧
    (∀ β : ℝ, 0 < β →
      ¬ {μ : Measure (Config (SiteVal U)) |
          IsGibbs β (Phi U) μ ∧ ¬ IsTranslationInvariantMeasure μ}.Countable)

def Universal (U : Machine) : Prop := ¬ ComputablePred (fun n : ℕ => 1 ≤ n ∧ U.HaltsOn n)

def CorollaryB : Prop :=
  ∀ U : Machine, Universal U →
    ¬ ComputablePred (fun p : ℕ × ℕ => 0 < p.2 ∧ ((p.1 : ℚ) / p.2) ∈ UniqueSet U) ∧
    (∃ f : ℕ → ℕ × ℕ, Computable f ∧ ∀ n, 0 < (f n).2 ∧ ((f n).1 : ℚ) / (f n).2 = betaN n) ∧
    ∀ n : ℕ, 1 ≤ n → (betaN n ∈ UniqueSet U ↔ ¬ U.HaltsOn n)

def ExistsUniversal : Prop := ∃ U : Machine, Universal U
```

Here `UniqueSet U` is the set 𝒰 of rational β > 0 at which βΦ has exactly one translation-invariant Gibbs measure. `Main.lean` proves

```lean
theorem UPD.theorem_A (h1 : H1) (h2 : H2) : TheoremA
theorem UPD.corollary_B (h1 : H1) (h2 : H2) : CorollaryB
theorem UPD.existsUniversal : ExistsUniversal
```

The statement file was written before the proofs and has not changed since (SHA-256 `ef3ebe7fc60c792f1297dcf9a4596504f5a365de5e45012df84da227fa01482b`).

| Printed result | Lean name | File (under `UndecidablePhaseDiagram/`) |
|---|---|---|
| Theorem A (Theorem 7.3, Lemma 7.1 and the properties of Φ) | `UPD.theorem_A` | `Main.lean` |
| Corollary B (Corollary 7.4) | `UPD.corollary_B` | `Main.lean` |
| A machine as in Section 2.2 exists | `UPD.existsUniversal`, from `UPD.Compiler.univMachine`, `univMachine_universal`, `univMachine_run_isSome` | `Main.lean`, `Compiler/Universal.lean` |
| Theorem 7.3 (i), (ii) and its last claim | `UPD.thm_main_i`, `UPD.thm_main_ii`, `UPD.thm_main_moreover` | `Proof/MainTheorem.lean` |
| Lemma 7.1 (a)–(d), Lemma 7.2 (a)–(c) | `UPD.windows_a` … `UPD.windows_d`, `UPD.thermal_a` … `UPD.thermal_c` | `Proof/Windows.lean`, `Proof/Thermal.lean` |
| Lemma 2.4 (Peierls), from `H2` | `UPD.Peierls.peierls` | `Peierls/Limit.lean` |
| Lemma 2.5 (Dobrushin), from `H1` | `UPD.Gibbs.IsingGraph.dobrushin_unique`, `UPD.Gibbs.IsingGraph.existsUnique_isDLR` | `Gibbs/Dobrushin.lean`, `Gibbs/Existence.lean` |
| Proposition 3.7 | `UPD.Scaffold.scaffold_ti_a`, `UPD.Scaffold.scaffold_ti_b`, `UPD.Scaffold.scaffold_ti_existsUnique` | `Scaffold/` |
| Lemma 5.5 (readiness) | `UPD.MachineM.ready_a`, `UPD.MachineM.ready_b` | `Background/Ready.lean` |
| Proposition 5.7, Lemma 5.8 | `UPD.BG.background_law`, `UPD.BG.background_rigid`, `UPD.BG.freeze_a`, `UPD.BG.freeze_b`, `UPD.BG.freeze_c` | `Background/` |
| Lemmas 6.1–6.3, Corollary 6.4 | `UPD.BG.pay_factor`, `UPD.Sensor.pay_sum` with `UPD.BG.Zf_ready`, `UPD.Gibbs.ElimData.elim`, `UPD.BG.pay_effective` | `Payload/`, `Gibbs/Elim.lean` |

`UndecidablePhaseDiagram/Audit.lean` lists 1,269 named results, these among them.

**Not formalized:** Section 8 (Lemma 8.1 and Proposition 8.2, the exact diagram), the Σ⁰₁-completeness of the halting set of U, Remarks 7.5 and 7.6, and the measurability clause of Lemma 5.8(b), which the formal proof does not use. Lemma 2.4 is proved with a cruder count of contours than the printed one; only the bound 1/3, which the paper uses, is proved.

## The hypotheses

`UndecidablePhaseDiagram/Hypotheses.lean` is the only place where a theorem of other authors enters. Each hypothesis is a proposition, quoted in its comment from the source:

- `H1`, Dobrushin's uniqueness theorem: for a countable index set, a finite spin set and a quasilocal specification whose Dobrushin constant is less than 1, any two compatible probability measures are equal. Source: S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems*, Cambridge 2017, Theorem 6.31, with Definitions 6.9, 6.11, 6.12 and 6.25.
- `H2`, the plus state of the two-dimensional Ising model: for every coupling J ≥ 0 there is a probability measure ν on {+1, −1}^(ℤ²) such that the plus expectations of every local function converge to their ν-integrals along every increasing sequence of finite sets that exhausts ℤ², ν is invariant under all translations, and ν satisfies the DLR identity of the Ising specification. Sources: Friedli and Velenik, Theorems 3.17 and 6.5, Example 6.51 and Lemma 6.65.

The quotations were checked against the authors' revised chapter files of that book. The specialization of `H1` to the Ising models of Lemma 2.5, the existence of Gibbs measures, the minus state, the spin flip and the Peierls bound are proved, not assumed. `UPD.existsUniversal` uses neither hypothesis.

## Choices in the formal statement

The formal statements render the printed ones with the following choices; Appendix D of the paper explains them.

- Theorem A is stated for every machine U and the interaction built from it; its proof does not use universality. Corollary B assumes only that the halting set of U is undecidable, which is what its proof uses. `ExistsUniversal` shows that such a machine exists.
- A machine has states `Fin (k + 1)` with initial state 0, which is not halting, and symbols `Fin (m + 2)` with blank 0 and the symbol 1. A move left from cell 0 ends the run without halting. The machine of `ExistsUniversal` never makes such a move.
- Gibbs kernels are finite sums over the fillings of a finite set, defined at every boundary condition. Test functions are real-valued, bounded and measurable. "Exactly one" is unique existence, "at least two" is the existence of two different measures, and "uncountably many" is "not countable".
- A rational number is presented by a pair (p, q) of natural numbers with q > 0. "𝒰 is not decidable" says that p/q ∈ 𝒰 is not a computable predicate of (p, q); "n ↦ β_n is computable" says that a computable map gives a pair presenting β_n.
- The interaction is a function of the machine; the remark that U enters it only through the table of M is not formalized. Colours, marks, bits and optional values are encoded by sum, option and Boolean types.

Each choice in the statement file is marked `[choice]` in a comment. All 29 `[choice]` comments of the development are listed in `evidence/CHOICES.json`.

Among the choices in the proofs, one changes the route of a printed argument: the existence halves of Steps 2 and 3 of the proof of Theorem 7.3 average translates of one Gibbs measure over boxes and take a cluster point, instead of the printed integral over Haar measure; Step 3 then separates the two measures by the expected number of plus spins in a block that contains a root of the chosen depth.

## What was checked

- **Pins.** Lean 4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, in `lean-toolchain`, `lakefile.lean` and `lake-manifest.json`.
- **Build.** All 75 modules of the development and `Challenge.lean`, `Solution.lean`, `Audit.lean` were compiled from source in one fresh serial run, one Lean process at a time with `-j1 -M6144`, against prebuilt Mathlib objects; all exited 0 (`evidence/BUILD.json`). Afterwards only `Challenge.lean` was rebuilt, after the fix described in `REPORT.md`; nothing imports it. `scripts/lint.sh` passes. The statement file is compiled unchanged with one option, `-Dbackward.isDefEq.respectTransparency=false` (`scripts/replay.py`), which Mathlib sets for the same derivation of `Fintype` instances.
- **Comparator.** `Challenge.lean` imports only Mathlib (twelve modules) and no file of this development. It contains `Statements.lean` and `Hypotheses.lean` byte for byte after their imports, each preceded by a `run_cmd` line that sets the module name under which the copied definitions are recorded. Two options are set around the copies: the option above, for the copy of `Statements.lean`, and `bootstrap.genMatcherCode false`, for the copy of `Hypotheses.lean`, so that Lean creates the same auxiliary matcher as in the separate module. The file then states `UPD.theorem_A (h1 : H1) (h2 : H2) : TheoremA`, `UPD.corollary_B (h1 : H1) (h2 : H2) : CorollaryB` and `UPD.existsUniversal : ExistsUniversal` with their proofs left as `sorry`. `Solution.lean` imports the proofs; `comparator.json` names the three theorems and permits only the three standard axioms. `lake comparator --config comparator.json` was run on Linux in a bubblewrap 0.9.0 sandbox. It made its own exports of both files, checked that the three proved theorems have exactly the statements of the challenge, with the same definitions, and use no other axiom, and replayed them in Lean's default kernel. It accepted them in 86.4 s. Records: `evidence/COMPARATOR.json`, `relay/results/comparator.log`, `relay/bwrap-invocations.ndjson`. A first run failed on a generated matcher name; it is kept in `relay/attempts/`.
- **Two kernel checkers.** The export of `Solution` for the three theorems (360,261,042 bytes, SHA-256 `82e35c6a00ef8668bee634d50b92251cad5727bb371cf7b15c4adef1e3178ddf`) contains every declaration on which they depend, Mathlib's included. `leanchecker` of Lean 4.35.0 (46.5 s) and `nanoda` (26.6 s, set to reject any axiom other than the three standard ones) each re-checked it and accepted it. The same `nanoda` run with `Classical.choice` not permitted rejects it. Records: `evidence/KERNEL-REPLAY.json`, `evidence/BINARY-DIGESTS.json`, `relay/kernels/`.
- **Axioms.** `Audit.lean` prints the axioms of the 1,269 named results of `UndecidablePhaseDiagram/Audit.lean`, the three final theorems first, checks the axioms of all 6,276 declarations of the development, private and generated ones included, and checks that the final theorems have the types `H1 → H2 → TheoremA`, `H1 → H2 → CorollaryB` and `ExistsUniversal`. Only `propext`, `Classical.choice` and `Quot.sound` occur. `AXIOMS.txt` is its complete output; `evidence/AXIOM-AUDIT.json` is its machine-readable form.
- **No admissions.** Apart from the three open proofs of `Challenge.lean`, no proof uses `sorry`; no file declares an axiom or uses `native_decide`, `implemented_by` or `extern` (`evidence/SOURCE-AUDIT.json`). The hypotheses `H1` and `H2` are definitions of propositions, passed as arguments.
- **Port.** The proofs were developed with Lean 4.30.0 and an earlier Mathlib, and ported to the pins above. The port changed the proofs of 70 of the 1,592 theorems and lemmas, in 26 of the 75 files; the bodies of four instances that prove a proposition; the body of one definition used only in proofs (`Scaffold.unif`, the uniform measure on a finite set, now built with a Mathlib construction that replaced a removed one, giving the same measure); and the class name in the header of one instance, which Mathlib renamed (`NoAtoms` to `NullSingletonClass`). No theorem statement changed. `Statements.lean` and `Hypotheses.lean` are byte for byte those of the development. Records: `evidence/PROOF-PRESERVATION.json` (with its method), `evidence/PORT.diff`, `evidence/FROZEN-STATEMENT.json`, `evidence/ORIGINAL-SOURCE.json`.
- **Dependencies.** All 10,268 dependency source files of the build match the list of SHA-256 hashes in `evidence/DEPENDENCY-SOURCES.json` (`DEPENDENCY-CHECK.json`). That list is byte for byte `lean/pins/DEPENDENCY-SOURCES.json` of release v1.4.0 of the forgetting paper (https://github.com/Apsiape/fixed-noise-ergodicity), whose check compared Mathlib's library sources byte for byte with the official commit. Mathlib was not rebuilt from source; the two kernel checkers re-check every Mathlib declaration that the proofs use.

`REPORT.md` is the full record of the port and of these checks.

## Historical reproduction workflow (optional)
The recorded runs used a Linux workspace in WSL on the authors' Windows machine, at `/opt/undecidable-phase-diagram-arxiv-2026-11-11`, with the toolchain, bubblewrap and the dependency directory `vendor/` copied from the workspace of the forgetting paper's release. That workspace holds what is not shipped here: `vendor/` (6.8 GB with build objects), the `.lake/` build objects, the 360 MB export and the logs of each compile.

You need the Lean 4.35.0 toolchain (`lean`, `lake`, `leanchecker`, `leanexport`), Python 3, Git, and at least 8 GiB of available memory.

1. Prepare `vendor/`. Follow steps 1 and 2 of `lean/README.md` of release v1.4.0 of the forgetting paper. Its `prepare_dependencies.py` checks every file against the same list as `evidence/DEPENDENCY-SOURCES.json` and writes the nine packages of `lake-manifest.json` into its `vendor/` directory; copy that directory here. Then, from this directory, run `lake exe cache get` for the Mathlib build objects. This route was not run for this directory; the recorded run used the copied `vendor/`.
2. Build: from this directory, `lake build`. It runs `scripts/replay.py`, which compiles the 75 modules and then `Challenge.lean`, `Solution.lean` and `Audit.lean`, one Lean process at a time, and writes the output of `Audit.lean` to `AXIOMS.txt`. Compare it with the shipped `AXIOMS.txt`. `bash scripts/lint.sh` repeats the source lint. The script refuses to start a compiler below 8 GiB of available memory. On Linux it also reads a heartbeat file `.host-memory.json` with the available memory of the Windows host, written by `relay/host-memory-monitor.py` in the recorded run; elsewhere on Linux that check needs the file or a local edit of the script.
3. Comparator, on Linux with bubblewrap: from this directory, `lake comparator --config comparator.json`. The comparator sandbox masks `/home`, `/root` and `/tmp`, so keep the directory outside them.
4. Kernel replays: export the solution with `lake env leanexport Solution -- …` and the target list of `evidence/KERNEL-REPLAY.json` (`export_command`), then run `leanchecker --from-export` on the export, and `nanoda_bin` with the configuration of `relay/kernels/nanoda.json`, its `export_file_path` set to the export.

The scripts in `relay/` ran the comparator, the export and the kernel checkers under a memory watchdog (`run-linux.py`, `linux_guard.py`, `bwrap-record`), generated `Challenge.lean` (`make_challenge.py`) and the root `Audit.lean` (`make_audit.py`), and wrote `evidence/` (`make_evidence.py`, `preservation.py`). They read the recorded workspace layout.

## Files

- `UndecidablePhaseDiagram.lean`, `UndecidablePhaseDiagram/`: the 75 modules of the development. `Statements.lean` is the statement file, `Hypotheses.lean` holds `H1` and `H2`, `Main.lean` proves the three final theorems, `Sanity.lean` tests the statement-level definitions. `Gibbs/` and `Peierls/` cover Section 2 (specifications, Lemmas 2.3–2.5, products over components, averaging), `Scaffold/` Section 3 and Appendix A, `Interaction/` the properties of Φ, `Background/` Section 5 and Appendix C, `Payload/` Section 6, `Proof/` Section 7, and `Compiler/` the universal machine of Section 2.2, built from Mathlib's halting problem and Mathlib's simulation of partial recursive functions by Turing machines, folded onto a one-sided tape with unary input.
- `Challenge.lean`, `Solution.lean`, `comparator.json`: the comparator check.
- `Audit.lean`, `UndecidablePhaseDiagram/Audit.lean`, `UndecidablePhaseDiagram/AuditCommand.lean`, `AXIOMS.txt`: the axiom audit and its output.
- `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`: the pins. `DEPENDENCY-CHECK.json`: the check of the dependency sources.
- `scripts/`: `replay.py` (the serial, memory-capped build that `lake build` runs, with `resource_guard.py` and the module list `modules.json`), `lint.sh`, and the shell helpers used during development (`build.sh`, `check.sh`, `env.sh`, `locked.sh`).
- `evidence/`: the records of the checks above. `evidence/AXIOMS.txt` and `evidence/DEPENDENCY-CHECK.json` are copies of the files of the same name in this directory.
- `relay/`: the scripts and receipts of the port and of the checks, and the failed first comparator run.
- `REPORT.md`: the record of the port and of the checks.

## What this directory leaves out, and paths

- Every file here except this README is byte for byte the file of the same path at commit `6dc5bfb` of the authors' development repository, the ported development with its records. This README replaces its reproduction note.
- The development's working records (`STATUS.md`, `BLUEPRINT.md`, `HANDOFF.md`: the log of the work sessions, the fidelity and proof choices with the lead agent's rulings, and notes on steps that the paper leaves implicit) are not included. `REPORT.md` and comments in the sources refer to them and to the work sessions; the choices that concern the statements are the `[choice]` comments of the sources and the comments of `Hypotheses.lean`. Some comments describe the state of the work when they were written; for example, `Main.lean` calls the main theorem "open". The audit records above are authoritative.
- Records and comments contain paths on the authors' machines: `/opt/…` paths of the WSL workspaces in `REPORT.md`, `evidence/`, `relay/`, `Audit.lean` and `scripts/replay.py`, the default WSL path in `relay/host-memory-monitor.py`, and the path of the forgetting paper's development in provenance comments of nine source files under `Compiler/` and `Scaffold/`. They name directories only and are kept so that every file is the verified one.

## License

Authored Lean sources and scripts: MIT or Apache 2.0, at your option. Documentation and recorded outputs: CC BY 4.0. See `../RIGHTS.md`, `../NOTICE` and the license files at the root of the repository. Third-party rights are unchanged.
