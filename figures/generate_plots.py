"""Render the manuscript's three experimental figures from saved observations.

Run normally from the portable plot-data.json, or use --refresh-data to rebuild
that snapshot from the local experiment archive. No solver or verifier is run.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from fractions import Fraction
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import font_manager
from matplotlib.lines import Line2D
from matplotlib.offsetbox import AnnotationBbox, HPacker, TextArea
from matplotlib.ticker import FixedLocator, FuncFormatter, NullFormatter

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SOURCE = ROOT / "experiments/results_complete_20260913/results.json"
DATA = HERE / "plot-data.json"
ALIASES = {"LP-CUT": "LP-CG", "SDP-CG": "SDP-CUT"}
COLORS = {"SDP-FULL": "#4477AA", "LP-CG": "#EE7733",
          "SDP-CUT": "#AA3377", "LP-CUT-CG": "#228833"}
METHODS = list(COLORS)
METHOD_STYLES = {"SDP-FULL": "-", "LP-CG": (0, (2, 1.3)),
                 "SDP-CUT": (0, (6, 2)), "LP-CUT-CG": "-"}
MODELS = ["M6", "M7-lift6", "M7-no5", "M7-all5"]
MODEL_COLORS = {"M6": "#4477AA", "M7-lift6": "#EE7733",
                "M7-no5": "#AA3377", "M7-all5": "#228833"}
MODEL_STYLES = {"M6": (0, (1, 1.7)), "M7-lift6": (0, (5, 1.6, 1, 1.6)),
                "M7-no5": (0, (4, 2)), "M7-all5": "-"}
GAP_LABEL = r"Gap above $5/9$"
BOUND_LABEL = r"Upper-bound estimate $U$"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def archive_path(raw):
    # Archived manifests contain Windows absolute paths, sometimes doubled.
    # Resolve the repository-relative suffix so the checkout can be relocated.
    parts = [p for p in raw.replace("\\", "/").split("/") if p]
    if ".research-repro" in parts:
        return ROOT.joinpath(*parts[parts.index(".research-repro"):])
    return Path(raw)


def snapshot():
    source = json.loads(SOURCE.read_text(encoding="utf-8"))
    rows = source["main_runs"] + [r for r in source["new_runs"]
                                  if r["phase"] in ("long", "reference")]
    assert len(source["main_runs"]) == 39 and len(rows) == 43
    runs = []
    for row in rows:
        cap = 21600 if row["phase"] == "long" else 3600
        path = archive_path(row["run_path"]) / "history.jsonl"
        history = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()]
        history = [h for h in history if h["eligible_for_budget"] and h["seconds"] <= cap]
        assert history and all(a["seconds"] <= b["seconds"] for a, b in zip(history, history[1:]))
        points, best = [], float("inf")
        for h in history:
            best = min(best, h["global_dual_upper"])
            points.append([h["seconds"], best])
        assert abs(best - row["numerical_global_upper"]) < 1e-12
        checkpoints = []
        for cp in source["checkpoints"]:
            if not all(cp.get(k) == row.get(k) for k in
                       ("model", "method", "repetition", "phase", "task_id")):
                continue
            eligible = [p[1] for p in points if p[0] <= cp["target_seconds"]]
            if cp["status"] != "verified":
                continue
            assert eligible and cp["target_seconds"] <= cap
            assert abs(min(eligible) - cp["numerical_upper"]) < 1e-12
            value = Fraction(cp["bound_fraction"])
            assert abs(float(value) - cp["bound_decimal"]) < 1e-14
            checkpoints.append([cp["target_seconds"], str(value)])
        assert checkpoints
        runs.append(dict(model=row["model"], method=ALIASES.get(row["method"], row["method"]),
                         repetition=row["repetition"], phase=row["phase"],
                         status=row["status"], budget_seconds=cap,
                         history=str(path.relative_to(ROOT)).replace("\\", "/"),
                         history_sha256=digest(path), points=points,
                         checkpoints=sorted(checkpoints),
                         final_exact_bound=row["exact_bound_fraction"]))
    data = dict(description="Budget-eligible best-so-far numerical U and verified rational bounds; no interpolation or averaging of repetitions.",
                source=str(SOURCE.relative_to(ROOT)).replace("\\", "/"),
                source_sha256=digest(SOURCE), runs=runs)
    DATA.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(f"Archived {len(runs)} runs, {sum(len(r['points']) for r in runs)} observations, "
          f"{sum(len(r['checkpoints']) for r in runs)} verified checkpoints.")


def style(font_dir=None):
    candidates = [Path(font_dir)] if font_dir else []
    if os.environ.get("LOCALAPPDATA"):
        candidates.append(Path(os.environ["LOCALAPPDATA"]) / "Programs/MiKTeX/fonts/opentype/public/lm")
    candidates += [Path("/usr/share/texmf/fonts/opentype/public/lm"),
                   Path("/usr/share/fonts/opentype/lmodern")]
    for folder in candidates:
        if (folder / "lmroman10-regular.otf").is_file():
            for name in ("lmroman10-regular.otf", "lmroman10-italic.otf", "lmroman10-bold.otf",
                         "lmmono10-regular.otf"):
                font_manager.fontManager.addfont(folder / name)
            break
    font_manager.findfont("Latin Modern Roman", fallback_to_default=False)
    font_manager.findfont("Latin Modern Mono", fallback_to_default=False)
    plt.rcParams.update({
        "font.family": "serif", "font.serif": ["Latin Modern Roman"], "font.size": 9,
        "font.monospace": ["Latin Modern Mono"],
        "mathtext.fontset": "custom", "mathtext.rm": "Latin Modern Roman",
        "mathtext.it": "Latin Modern Roman:italic", "mathtext.bf": "Latin Modern Roman:bold",
        "mathtext.tt": "Latin Modern Mono", "mathtext.fallback": "cm",
        "axes.titlesize": 10, "axes.titlepad": 9, "axes.labelsize": 9,
        "xtick.labelsize": 8, "ytick.labelsize": 8, "legend.fontsize": 8.5,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.linewidth": .65, "axes.edgecolor": "#454545",
        "xtick.major.width": .6, "ytick.major.width": .6,
        "xtick.minor.width": .4, "ytick.minor.width": .4,
        "xtick.major.size": 3, "ytick.major.size": 3,
        "axes.unicode_minus": False, "axes.axisbelow": True,
        "legend.frameon": False, "legend.handlelength": 2.8,
        "legend.columnspacing": 1.4, "legend.labelspacing": .5,
        "pgf.texsystem": "pdflatex", "pgf.rcfonts": False,
        "pgf.preamble": r"\usepackage[T1]{fontenc}\usepackage{lmodern}",
        "svg.fonttype": "path", "svg.hashsalt": "turan-paper",
        "path.simplify": False,
        "savefig.facecolor": "white",
    })


def panels(count=2, *, height=3.25, sharey=False, gap=.24):
    fig, axes = plt.subplots(1, count, figsize=(6.5, height), sharey=sharey)
    fig.subplots_adjust(left=.105, right=.975, bottom=.28, top=.89, wspace=gap)
    return fig, axes


def experiment_title(ax, name, description=""):
    if not description:
        ax.set_title(name, fontfamily="monospace")
        return
    # Separate text objects preserve the manuscript's texttt face for names
    # and its roman face for prose in both the TeX PDF and SVG backends.
    title = HPacker(children=[
        TextArea(name, textprops={"family": "monospace", "size": 10}),
        TextArea(description, textprops={"family": "serif", "size": 10}),
    ], align="baseline", pad=0, sep=0)
    ax.add_artist(AnnotationBbox(title, (.5, 1), xybox=(0, 9),
                                xycoords="axes fraction", boxcoords="offset points",
                                box_alignment=(.5, 0), frameon=False))


def experiment_legend(legend):
    for label in legend.get_texts():
        if label.get_text() in METHODS + MODELS:
            label.set_fontfamily("monospace")


def axis(ax, *, logx=True, logy=False, xlim=(8, 4300), ylim=None, ticks=None):
    ax.set_xscale("log" if logx else "linear")
    ax.set_yscale("log" if logy else "linear")
    ax.set_xlim(*xlim)
    if ylim:
        ax.set_ylim(*ylim)
    ax.set_xlabel("Search time (s)", labelpad=5)
    ax.grid(True, which="major", color="#e5e5e5", linewidth=.55)
    if ticks is not None:
        ax.xaxis.set_major_locator(FixedLocator(ticks))
        ax.xaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{v:g}"))
    ax.xaxis.set_minor_formatter(NullFormatter())
    ax.yaxis.set_minor_formatter(NullFormatter())
    if not logy:
        ax.ticklabel_format(axis="y", style="plain", useOffset=False)


def curves(ax, rows, *, gap=False, distinguish_models=False, carry_single=False):
    offset = 5 / 9 if gap else 0
    for row in rows:
        color = MODEL_COLORS[row["model"]] if distinguish_models else COLORS[row["method"]]
        ls = MODEL_STYLES[row["model"]] if distinguish_models else METHOD_STYLES[row["method"]]
        times, values = map(list, zip(*row["points"]))
        values = [v - offset for v in values]
        if len(times) > 1 or carry_single:
            ax.step(times + [row["budget_seconds"]], values + [values[-1]],
                    where="post", color=color, ls=ls, lw=1.0, alpha=.8)
        if row["method"] == "SDP-FULL":
            ax.plot(times[0], values[0], marker="o", ms=4.3, mfc="white",
                    mec=color, mew=.9, linestyle="none", zorder=5)
        ax.plot([c[0] for c in row["checkpoints"]],
                [float(Fraction(c[1])) - offset for c in row["checkpoints"]],
                linestyle="none", marker="x", ms=4.3, mew=.9, color=color, zorder=6)


def method_handles(names=METHODS):
    return [Line2D([], [], color=COLORS[n], lw=1.3, ls=METHOD_STYLES[n],
                   marker="o" if n == "SDP-FULL" else None, mfc="white", ms=4.3,
                   label=n) for n in names]


def model_handles(names=MODELS):
    return [Line2D([], [], color=MODEL_COLORS[n], lw=1.3,
                   ls=MODEL_STYLES[n], label=n) for n in names]


def common_legend(fig, handles, columns=4):
    experiment_legend(fig.legend(handles=handles, loc="lower center",
                                 bbox_to_anchor=(.54, .025), ncol=columns))


def export(fig, name, preview_dir):
    # The fixed 6.5-inch canvas is inserted at full manuscript width; tight
    # cropping would change the scale of every font in the final paper.
    for ext in ("pdf", "svg"):
        metadata = {"Creator": "generate_plots.py"}
        metadata.update({"CreationDate": None, "ModDate": None} if ext == "pdf" else {"Date": None})
        target = HERE / f"{name}.{ext}"
        # TeX embeds Latin Modern Type 1 fonts correctly. Matplotlib's native
        # Type 42 PDF embedding misidentifies the CFF-based OpenType fonts.
        fig.savefig(target, metadata=metadata, **({"backend": "pgf"} if ext == "pdf" else {}))
        if ext == "svg":
            target.write_text("\n".join(line.rstrip() for line in target.read_text(encoding="utf-8").splitlines()) + "\n",
                              encoding="utf-8")
    if preview_dir:
        preview_dir.mkdir(parents=True, exist_ok=True)
        fig.savefig(preview_dir / f"{name}.png", dpi=180)
    plt.close(fig)


def render_sdp_comparison(production, preview_dir):
    fig, ax = panels(1, height=3.5)
    # Keep the original two-panel axes width and font scale, with side margins.
    panel_width = (.975 - .105) / (2 + .43)
    fig.subplots_adjust(left=.54 - panel_width / 2, right=.54 + panel_width / 2)
    curves(ax, [r for r in production if r["method"] == "LP-CUT-CG"], distinguish_models=True)
    axis(ax, xlim=(1, 4800), ylim=(.558, .5642), ticks=[1, 10, 100, 1000, 3600])
    ax.set_ylabel(BOUND_LABEL)
    experiment_title(ax, "LP-CUT-CG")
    experiment_legend(fig.legend(handles=model_handles(), loc="lower center",
                                 bbox_to_anchor=(.54, .025), ncol=2,
                                 columnspacing=1.0, handlelength=2.5))
    export(fig, "sdp-comparison", preview_dir)


def render(runs, preview_dir):
    production = [r for r in runs if r["phase"] == "production"]
    assert len(production) == 39
    for model in MODELS:
        for method in (METHODS if model != "M7-lift6" else ["LP-CUT-CG"]):
            assert sorted(r["repetition"] for r in production
                          if (r["model"], r["method"]) == (model, method)) == [1, 2, 3]

    fig, axes = panels(sharey=True, gap=.13)
    for ax, model in zip(axes, ("M7-no5", "M7-all5")):
        curves(ax, [r for r in production if r["model"] == model], gap=True)
        axis(ax, logy=True, ylim=(.0028, .55), ticks=[10, 100, 1000, 3600])
        experiment_title(ax, model)
    axes[0].set_ylabel(GAP_LABEL)
    common_legend(fig, method_handles())
    export(fig, "seven-methods", preview_dir)

    render_sdp_comparison(production, preview_dir)

    fig, axes = panels(3, height=3.35, sharey=True, gap=.16)
    long_runs = [r for r in runs if r["phase"] == "long"]
    for ax, model in zip(axes, ("M7-no5", "M7-all5", "M6")):
        curves(ax, [r for r in long_runs if r["model"] == model], gap=True)
        axis(ax, logy=True, xlim=(8, 33000), ylim=(.002, .16), ticks=[60, 600, 3600, 21600])
        experiment_title(ax, model)
    reference = next(r for r in runs if r["phase"] == "reference")
    axes[2].plot(reference["points"][0][0], float(Fraction(reference["final_exact_bound"])) - 5 / 9,
                 marker="s", ms=4.5, mfc="white", mec=COLORS["SDP-FULL"], mew=1, ls="none", zorder=6)
    axes[0].set_ylabel(GAP_LABEL)
    handles = method_handles(["LP-CUT-CG", "SDP-FULL"]) + [
        Line2D([], [], color="#454545", marker="x", ms=4.3, ls="none", label="Verified bound"),
        Line2D([], [], color="#454545", marker="s", mfc="white", ms=4.5, ls="none",
               label="Independent one-hour reference")]
    common_legend(fig, handles, columns=2)
    export(fig, "long-runs", preview_dir)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh-data", action="store_true")
    parser.add_argument("--font-dir", type=Path)
    parser.add_argument("--preview-dir", type=Path)
    args = parser.parse_args()
    if args.refresh_data:
        snapshot()
    data = json.loads(DATA.read_text(encoding="utf-8"))
    style(args.font_dir)
    render(data["runs"], args.preview_dir)
    print("Rendered three PDF/SVG figures at manuscript width.")


if __name__ == "__main__":
    main()
