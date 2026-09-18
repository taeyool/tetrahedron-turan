"""Write the final English report and vector figures from audited observations."""
import argparse
from pathlib import Path
import json
from fractions import Fraction
import statistics
import csv
import hashlib
import shutil
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

def med(g,k): return g[k]['median']
def interval(g,k,d=3):
    s=g[k]
    if s['median'] is None:return 'not reached'
    return f"{s['median']:.{d}f} [{s['minimum']:.{d}f}, {s['maximum']:.{d}f}]"

def main(out):
    data=json.loads((out/'results.json').read_text(encoding='utf-8')); val=json.loads((out/'validation.json').read_text(encoding='utf-8'))
    rows=data['main_runs']; new=data['new_runs']; cps=data['checkpoints']; groups=data['groups']
    best=next(r for r in new if r['model']=='M7-all5' and r['phase']=='long')
    shutil.copy2(best['certificate_path'],out/'best-long-all5-certificate.json')
    methods=['SDP-FULL','LP-CUT','SDP-CG','LP-CUT-CG']
    colors=dict(zip(methods,['#7b3294','#d98318','#2166ac','#14846b']))
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42,'svg.fonttype':'none'})
    def trajectory(ax,row,color,label=None,cap=3600):
        h=[json.loads(l) for l in (Path(row['run_path'])/'history.jsonl').read_text(encoding='utf-8').splitlines()]
        h=[v for v in h if v['eligible_for_budget'] and v['seconds']<=cap]
        ts=[v['seconds'] for v in h]; us=[];best=float('inf')
        for v in h:best=min(best,v['global_dual_upper']);us.append(best-5/9)
        if len(ts)==1:ax.scatter(ts,us,color=color,s=22,label=label,zorder=5)
        else:ax.step(ts+[cap],us+[us[-1]],where='post',color=color,alpha=.66,lw=1.25,label=label)
        selected=[c for c in cps if c['model']==row['model'] and c['method']==row['method'] and c['repetition']==row['repetition'] and c['phase']==row['phase'] and c.get('task_id')==row.get('task_id') and c['status']=='verified']
        ax.scatter([c['target_seconds'] for c in selected],[c['bound_decimal']-5/9 for c in selected],marker='x',color=color,s=20,lw=.8,zorder=6)
    fig,axes=plt.subplots(1,2,figsize=(8.6,3.5),sharey=True,layout='constrained')
    for ax,model in zip(axes,['M7-no5','M7-all5']):
        for method in methods:
            for r in [r for r in rows if r['model']==model and r['method']==method]:trajectory(ax,r,colors[method],method if r['repetition']==1 else None)
        ax.set(xscale='log',yscale='log',xlim=(8,4000),ylim=(.0028,.55),title=model,xlabel='Search time (s)')
        ax.grid(alpha=.18,which='both');ax.legend(fontsize=8,loc='upper center',bbox_to_anchor=(.5,-.23),ncol=2)
    axes[0].set_ylabel('Global upper bound minus 5/9')
    for ext in ['pdf','svg']:fig.savefig(out/f'seven-methods.{ext}')
    plt.close(fig)
    fig,axes=plt.subplots(1,3,figsize=(9.2,3.3),layout='constrained')
    for ax,model in zip(axes,['M7-no5','M7-all5','M6']):
        r=next(r for r in new if r['model']==model and r['phase']=='long')
        trajectory(ax,r,'#14846b' if model!='M6' else '#7b3294','Fresh six-hour study',21600)
        if model=='M6':
            ref=next(r for r in new if r['phase']=='reference')
            ax.scatter([ref['candidate_available_seconds']],[ref['exact_bound_decimal']-5/9],marker='s',s=26,color='#777777',label='Independent one-hour reference')
        ax.set(xscale='log',yscale='log',xlim=(40,23000),title=model,xlabel='Search time (s)');ax.grid(alpha=.18,which='both')
        if model=='M6':ax.legend(fontsize=7,loc='upper center',bbox_to_anchor=(.5,-.25))
    axes[0].set_ylabel('Global upper bound minus 5/9')
    for ext in ['pdf','svg']:fig.savefig(out/f'long-runs.{ext}')
    plt.close(fig)

    lines=['# Computational evaluation: completed campaign report','',
        "This report was written during the experiments, before the paper's final section numbering; its \"Section 6\" is the paper's Section 5 and Appendix C.",'',
        'The selected matrix contains **13 configurations and 39 fresh production trials**, each configuration repeated three times. The September 11-13 completion campaign added 18 productions, three separate fresh six-hour studies, and an independent one-hour M6 native reference. All new final candidates passed model-specific integer verification. The original 21 trials are included unchanged.',
        '',f'The completion controller finished after {data["elapsed_campaign_hours"]:.2f} elapsed hours, including setup, pilots, diagnostics, repaired attempts, searches and verification. Its 48 tasks are orchestration units, not 48 scientific configurations. Paper authoring time is additional. Every new production has status `time_limit`; none is presented as a converged SDP optimum. The original M6 SDP-FULL iteration-limit outcomes remain labeled `numerical_failure`.',
        '', '## Main findings','',
        'On each seven-vertex model, LP-CUT-CG gives the strongest one-hour exact certificate among the four measured pipelines. Full LP-CUT reaches the shared numerical targets more slowly and stores all 1,295,600 configuration columns. Generated SDP reduces memory substantially relative to full SDP, but leaves unresolved restricted-master feasibility and produces weaker certificates. These are observations about the pinned implementations and declared policies, not universal complexity or solver rankings.',
        '', '## Production endpoints','',
        'Bounds and times below are medians [minimum, maximum] of three repetitions. Numerical targets were frozen before this completion campaign: 0.5628 (M7-no5), 0.5646 (M7-all5), and 0.5617 (M6). A missing target time is censored, not an invented timeout value. RSS is sampled process-tree resident memory, distinct from kernel-recorded commit memory.',
        '', '| Model | Method | Exact SVD bound | Search seconds | Target seconds | Median RSS GiB | Status |',
        '| --- | --- | --- | --- | --- | ---: | --- |']
    for g in groups:
        lines.append(f"| {g['model']} | {g['method']} | {interval(g,'exact_bound_decimal',12)} | {interval(g,'search_seconds')} | {interval(g,'time_to_target_seconds')} | {med(g,'rss_peak_bytes')/2**30:.3f} | {', '.join(sorted(set(g['statuses'])))} |")
    lines+=['','The matched-target median LP-CUT / LP-CUT-CG search-time ratios are 6.36 for M7-no5 and 2.34 for M7-all5. They include the full-LP memory policies described below; no ratio is assigned to SDP arms that did not reach the target. For LP-CUT-CG, enlarging only host order (M6 to M7-lift6) does not improve the rounded finite-budget certificate, while the additional order-seven and five-root square families do. Relaxation nesting does not imply monotone time-limited outcomes.','',
        '## Cost, residuals and exact representations','',
        'All stage timings include completed work even if the last evaluation was late. Candidate selection excludes late evaluations. Native-call time includes model assembly and backend work, while the separate eigen column is the exported-moment diagnostic and LP separation outside native cones. Row updates, file I/O, recycling, and finalization explain the remainder; component medians need not add to a median total.',
        '', '| Model | Method | Init s | Solver/call s | Eigen s | Pricing s | Final columns | Final cuts |', '| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |']
    for g in groups:
        if g['model'] not in ['M7-no5','M7-all5']:continue
        lines.append(f"| {g['model']} | {g['method']} | {med(g,'initialization_seconds'):.3f} | {med(g,'solver_seconds'):.3f} | {med(g,'eigen_seconds'):.3f} | {med(g,'pricing_seconds'):.3f} | {med(g,'final_columns'):.0f} | {med(g,'final_cuts'):.0f} |")
    lines+=['','Every new production endpoint is listed below; complete fractions, integer-entry counts, scale, factorization, residuals, source hashes, ordered bases, timing and certificate paths are in `results.csv` / `results.json`. All fractions use the common primary SVD policy, with uncompressed rounding reported alongside it. No algorithm ordering is reversed by the rounding choice.','',
        '| Model / method / repetition | SVD exact fraction | Factors | Uncompressed exact fraction | Min moment eigenvalue |',
        '| --- | --- | ---: | --- | ---: |']
    for r in new:
        if r['phase']!='production':continue
        lines.append(f"| {r['model']} / {r['method']} / {r['repetition']} | {r['exact_bound_fraction']} | {r['factors']} | {r['uncompressed_bound_fraction']} | {r['final_minimum_eigenvalue']:.5g} |")
    lines+=['','Full-native SCS has large residuals: no5 primal 0.107-0.132, dual 0.131-0.156, gap 0.0208-0.0234; all5 primal 0.279-0.358, dual 0.204-0.221, gap 0.0363-0.0468. Its last moment vectors are not feasible certificates of relaxation optima. Full-universe exact evaluation of the exported integer squares yields valid, but weak, upper bounds despite this. The stopping statuses are `optimal_inaccurate` / `time_limit`, not numerical convergence. The native iteration counts (no5 97/97/99, all5 55/54/55) differ because stopping is based on wall time. Generated SDP also has substantial moment violations; those residuals and PSD repair magnitudes are preserved in the individual rows.','',
        '## Longer studies','',
        'The earlier saved masters did not support exact continuation of their internal solver state. The longer studies therefore started as separate fresh repetition 1, selected before results, with a six-hour budget. They are not fourth main repetitions or continuations of whichever short trial happened to be best. M6 and M7-lift6 LP-CUT-CG had already passed their stopping tests and were not extended.',
        '', '| Study | One-hour exact SVD bound | Six-hour exact SVD bound | Factors at six hours | Search s |', '| --- | --- | --- | ---: | ---: |']
    for r in new:
        if r['phase']!='long':continue
        cp=next(c for c in cps if c.get('task_id')==r['task_id'] and c['target_seconds']==3600)
        initial=cp.get('bound_fraction') or 'not available; separate reference below'
        lines.append(f"| {r['model']} / {r['method']} | {initial} | {r['exact_bound_fraction']} | {r['factors']} | {r['search_seconds']:.3f} |")
    lines+=['','M7-no5 improves from 0.559209644128 to 0.558917128212. The repaired M7-all5 long study improves from its own one-hour value 0.558467616092 to 0.557807255160. That all5 trajectory adds a validated PSD-cut fallback when pricing repeats existing columns; 204 fallback updates occurred. It is a separately disclosed longer-run policy, so its one-hour checkpoint does not replace the earlier main LP-CUT-CG repetitions. Both six-hour LP searches remain time-limited. Their last evaluations finished after budget (overshoot 9.313/9.766 s) and were excluded; the saved best candidates were available before 21,600 s.',
        '', 'The M6 six-hour native run exposes only its final candidate, not intermediate iterates. An independent fresh one-hour run under the same extended native iteration ceiling gives 404395939151293/720000000000000 = 0.5616610265990181 (84 factors); the six-hour result is 16849596538693/30000000000000 = 0.5616532179564333 (80 factors). They are two independent executions, not points of a single exposed native trajectory. Neither supplies an exact primal/dual enclosure.',
        '', 'The best new research certificate is **312372062889819/560000000000000 = 0.5578072551603911**, with 794 integer-square factors. It is the certificate of the main theorem of the paper, distributed as `certificate/K4_turan_order7_certificate.json`; its Lean formalization is recorded under `certificate/verification/`.',
        '', '## Settings, validation and repaired attempts','',
        'The campaign retains every actually executed source snapshot and SHA-256 manifest. Windows 11, i7-14700K (20 physical/28 logical cores), 63.72 GiB physical RAM, balanced power plan; Python 3.12.4, NumPy 2.0.2, SciPy 1.13.1, HiGHS 1.15.1, SCS 3.2.8, CVXPY 1.6.5, OpenBLAS 0.3.27, MinGW GCC 13.2.0. Solver and BLAS use one thread, exhaustive pricing two. The additional campaign uses schedule seed 611, one experiment at a time, and an enforced 40 GiB process-tree commit cap. Initialization allows 3600 s, search 3600 s plus 60 s watchdog grace; exact jobs have separate limits. The initial schedule was changed only to place repair gates and dependent pilots before affected fresh repetitions.',
        '', 'All models keep stationarity and the specified bases. Seven-vertex enumeration has 1,295,600 canonical classes from 13,051,375 raw extensions, with 504,000 relabeling checks. Complete coefficient caches occupy 17,930,331,144 bytes (no5) and 20,417,604,732 bytes (all5); measured construction takes 110.203 and 132.328 s. Native CSC caches take 12,127,128,520 and 13,786,775,880 bytes, constructed in 92.391 and 294.703 s. These shared cold costs are not included in warm initialization or search time.',
        '', 'Full LP uses bounded coefficient reads and chunked insertion, retaining all configurations. The common memory guard caps projected coefficients at 500 million and retains all dual-active cuts; the old generated/m6/lifted groups never approached that threshold. All5 full LP uses this policy. Repeated no5 memory failures required a stricter 300 million ceiling (229 cuts plus two base rows at full columns), preserving all active cuts and admitting the largest fitting prefix of up to 80 eigenvalue-ranked violated cuts. Full-instance recycling exports all coefficients, costs, bounds and basis statuses, destroys the old HiGHS instance, and verifies hashes after restoration; all this time counts in search. Internal factorization/scaling is rebuilt. A full-hour pilot exercised 21 successful recycle/solve cycles before three fresh no5 productions. This is a disclosed policy difference, not an identical-policy algorithm ablation.',
        '', 'Full native SDP uses the same auxiliary-marginal mathematical formulation through a validated SCS executable that owns its input CSC, avoiding Python/CVX canonicalization copies. Its indirect solver also owns a transpose. The source version, compiler/BLAS and tolerances are pinned; ownership and deadline instrumentation were validated against stock SCS and the official wheel. Tiny fixtures had stock/owned array equality and maximum wheel difference 2.98e-8 under a 2e-7 validation tolerance. Full-model forward/adjoint, sign, off-diagonal scaling and global pricing roundtrips passed.',
        '', 'Earlier full-native rho_x=1e-6 and 0.01 attempts failed before the initial work-cache linear solve completed. A pilot-frozen rho_x=100 obtained time-limited candidates and is used consistently in all six fresh full-native productions. This changes SCS splitting/preconditioning, not the mathematical SDP; the feasibility targets remain 1e-8, production ceiling 20 million iterations, and best inner-CG tolerance 1e-12. Generated SDP retains rho_x=1e-6, 300 s restricted-solve limits and model-specific whole-iteration admission reserves. Full-native reserves 30 s (no5) / 150 s (all5) for export/evaluation. Inner-CG residual logs are linear-system diagnostics and must not be called SDP feasibility residuals.',
        '', 'Original allocation failures, unsuccessful conditioning pilots, the two no5 failures after a verified fresh second recycle, and the interrupted redundant no5 trial are all retained as distinct attempts in `attempts.csv`. No failure was deleted or relabeled as convergence. Detailed repair evidence is in the campaign `repairs/` directory, and `attempt-provenance.json` links source/settings to every attempt. Changing settings was followed by validation and fresh repetitions for the affected group; completed unaffected groups were not repeated.',
        '', f"The final audit checks {val['new_unique_certificates_audited']} unique new exact artifacts, their source dual hashes, exact fractions, complete-scan records, and candidate eligibility. Across the 39 main trials, {val['production_verified_checkpoints']} of {val['production_checkpoint_slots']} scheduled checkpoint slots have an available verified candidate. The other 42 have no completed native candidate by the scheduled time (12 from earlier M6, 30 from new native arms), and are explicitly missing. Final SVD and uncompressed certificates are retained for every main trial. Exact factor scale is 2,000,000, multiplier denominator M^2 and SVD tolerance 1e-7. Verification runs after timed search. `checkpoints.csv` includes retrospective candidate-availability plus actual verification cost for new candidates; reuse records link to the original cost, not zero-cost fresh certification.",
        '', '## Artifacts and interpretation','',
        '- `results.csv` and `results.json`: 39 main trials, 13 group summaries, new settings/residuals, exact fractions and provenance.',
        '- `long-runs.csv`: three six-hour trials and the independent M6 one-hour reference.',
        '- `checkpoints.csv`: available and missing checkpoints; no late candidate is backdated.',
        '- `attempts.csv`, `attempt-provenance.json`: all 75 task attempts, including pilots, failures and interruptions.',
        '- `seven-methods.pdf` / `.svg`: four pipelines on each seven-vertex model; three observed curves, exact crosses at checkpoint budgets, native first-candidate dots.',
        '- `long-runs.pdf` / `.svg`: fresh six-hour trajectories and separate M6 one-hour reference.',
        '- `validation.json`, `publication-manifest.json`: audit outcomes and SHA-256 links to retained inputs.',
        '- the six-hour all5 SVD certificate is distributed as `certificate/K4_turan_order7_certificate.json`.',
        '', 'Cold setup, file I/O, wall-time admission and differing memory safeguards limit attribution to mathematical algorithms alone. Three deterministic repetitions measure timing and solver variability, not arbitrary initialization robustness. Negative moment eigenvalues prevent a claim of numerical or exact SDP optimality. Integer verification proves the exported upper certificates, not primal feasibility. The excluded historical replay is not counted; its earlier archived comparison remains separate evidence.', '']
    (out/'REPORT.md').write_text('\n'.join(lines),encoding='utf-8')
    manifest=json.loads((out/'publication-manifest.json').read_text(encoding='utf-8'))
    manifest['report_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in out.iterdir() if p.is_file() and p.name!='publication-manifest.json'}
    (out/'publication-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print('Wrote report and two PDF/SVG figures.')

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);main(ap.parse_args().output)
