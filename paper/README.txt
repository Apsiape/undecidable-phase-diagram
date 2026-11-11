An uncomputable phase diagram at positive temperature for one classical lattice model
Seth Douglas and Nidhal Mghirbi
Version 1.1.0, November 2026

Build: python -B build.py [--build-dir NEW_OR_EMPTY_DIRECTORY]
Requires Python 3, pdflatex and the LaTeX packages named in preamble-core.tex. No BibTeX run is
needed; the bibliography is inline (sections/references.tex). The build runs pdflatex three times
without shell escape and rejects warnings, unresolved references and overfull or underfull boxes.
main.pdf is the compiled preprint (43 pages). main.tex inputs preamble-core.tex and the files in
sections/. abstract.txt is the abstract as plain text.
Some recent LaTeX releases apply a first-aid patch to cleveref (hook chunk firstaid/cleveref) that
names every theorem-like environment "Theorem" in cross-references. build.py removes that patch
for the run; with plain "pdflatex main.tex" such releases may print "Theorem" where the paper
means Proposition, Lemma or Corollary. The mathematics is unaffected either way.
No proof uses a computation. No publication or submission is performed by the build.
