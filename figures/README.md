# Manuscript figures

Regenerate the three experimental figures with:

```sh
python figures/generate_plots.py
```

Dependencies: Python, Matplotlib, pdfLaTeX with PGF and Latin Modern, and the
Latin Modern OpenType fonts from TeX Live or MiKTeX. Use `--font-dir PATH`
if the fonts are installed elsewhere.
PDF and SVG outputs are written here. The manuscript includes the PDFs at
full text width. `relabel_sdp_comparison.py` is a compatibility entry point
for this same generator.

## Data

`plot-data.json` is a portable extraction of the archived experiment records:
39 one-hour production runs (13 configurations, three repetitions each),
three six-hour runs, and one independent one-hour M6 reference. It stores
all budget-eligible best-so-far numerical observations and exact rational
checkpoint bounds, together with source paths and SHA-256 hashes.

The checked-in snapshot is sufficient to render all three figures. The archived
histories and certificates are now in [the evidence bundle](../experiments/evidence/README.md).
`--refresh-data` remains a historical import operation and expects the original
private campaign layout, not the portable evidence bundle:

```sh
python figures/generate_plots.py --refresh-data
```

Extraction checks the final numerical minima against the published summary,
checkpoint eligibility and numerical values, and exact fractions against
their stored decimal values. It runs no optimization or certificate verifier.
The campaign report and figures under `experiments/results_complete_20260913/` are preserved.
Legacy method identifiers `LP-CUT` and `SDP-CG` are mapped to the manuscript's
`LP-CG` and `SDP-CUT`, respectively, before assigning visual styles.

## Figure conventions

- Canvas width: 6.5 inches, equal to the manuscript text width. Do not use
  tight cropping or shrink the PDFs on insertion, as that rescales the fonts.
- Font: Latin Modern Roman; matching math fonts. Titles 10 pt, axis labels
  9 pt, ticks 8 pt, legends 8.5 pt. SVG glyphs are paths; PDFs use Matplotlib's
  PGF/pdfLaTeX backend to embed the same Type 1 fonts as the manuscript.
  Experiment and method names in titles and legends use Latin Modern Mono,
  rendered as `\ttfamily` in PDF to match the manuscript's `\texttt` names.
  Descriptive text retains the roman font.
- Method colors: SDP-FULL blue `#4477AA`, LP-CG orange `#EE7733`, SDP-CUT
  purple `#AA3377`, LP-CUT-CG green `#228833`.
- Method comparisons also distinguish lines by dash pattern. When comparing
  SDPs under LP-CUT-CG, use fixed SDP colors and patterns: M6 blue `#4477AA`
  dotted, M7-lift6 orange `#EE7733` dash-dot, M7-no5 purple `#AA3377` dashed,
  M7-all5 green `#228833` solid. Apply this same mapping to both the four-SDP
  comparison and the one-hour trajectories. The method comparison and the
  long-run panels retain method colors, identified by their method legends.
- Every repetition remains a separate thin trajectory; no averaging, smoothing,
  time shifts, or artificial separation of overlapping observations.
- Step curves show the smallest numerical U available by each search time.
  Carry forward the final value to the budget, as in the archived figures.
  Lone SDP-FULL observations in the seven-vertex and six-hour comparisons
  remain points, without fabricated trajectories.
- Crosses show exact certificate bounds at checkpoint budgets; verification
  time is additional. Open circles identify first SDP-FULL candidates.
  The open square in the long-run comparison is the separate M6 one-hour
  reference, at its candidate availability time.
- Axes: `Search time (s)`, `Gap above 5/9` for U - 5/9, and
  `Upper-bound estimate U` for U. The long-run panels share the same y range.
- Legends below the plots; shared legends when the panels compare the same
  entities. No panel letters. Only light major grid lines; no top/right frame.

For PNG previews, add `--preview-dir PATH`. Inspect the final manuscript PDF
as well as the standalone figures after making changes.
