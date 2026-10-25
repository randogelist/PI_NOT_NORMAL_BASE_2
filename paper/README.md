# Research preprint

[Read the PDF](pi_ct_preprint.pdf) · [Editable LaTeX source](pi_ct_preprint.tex)

**The C_t Route toward Binary Non-Normality of Pi: Formalized analytic progress and an explicit residual-tail criterion**

Version 1, 25 October 2026. This preprint presents the anchored analytic coefficient, its quantitative error bounds, a finite alternating-word inequality, and the conditional non-normality endpoint. The required actual-pi residual-tail estimate remains open.

The manuscript fixes its verified Lean baseline at commit 1ce84cb63dc48e43ed92901c29a60f6d07ed4d9b, [successful hosted run 40175464758](https://github.com/randogelist/PI_NOT_NORMAL_BASE_2/actions/runs/40175464758). Its 71 modules were freshly compiled in the preceding hosted run, then reused after fingerprint checks and audited again at this baseline. [verification-baseline.json](verification-baseline.json) records the evidence; [theorem-map.json](theorem-map.json) records the statement-to-source correspondence.

The preprint is a repository research manuscript. It has not been submitted to an external preprint server, assigned a DOI, or peer reviewed.

## Build the document

With pdflatex and the packages listed in the source installed:

~~~sh
make -C paper
~~~

This builds only the PDF. It never invokes Lean or Lake. All Lean compilation and axiom audits remain exclusive to this repository's GitHub Actions runner.

The checked-in PDF accompanies its editable source. The fixed baseline identifies the mathematical evidence used when preparing this version; later repository CI runs do not silently change that citation.
