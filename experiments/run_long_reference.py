"""Independent M6 native references with the same SDP and a larger SCS iteration cap.

Separate fresh reference: the previous SCS internal iterate was not retained.
The changed cap is disclosed and is not pooled into the one-hour comparison.
"""
import argparse
import inspect
from pathlib import Path
import time
import runtime as rt
import run_remaining_method as original


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cache',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--seconds',type=float,default=21600)
    a=p.parse_args()
    source=inspect.getsource(original.native_solve).replace('max_iters=1000000,','max_iters=20000000,')
    scope=dict(original.__dict__);exec(compile(source,__file__,'exec'),scope)
    original.native_solve=scope['native_solve']
    a.model='M6';a.method='SDP-FULL';a.rep=1
    a.phase='long_reference' if a.seconds>3600 else 'reference'
    rt.CHECKPOINTS=[t for t in [60,300,900,1800,3600,7200,14400,21600] if t<=a.seconds]
    original.run(a)
    path=a.output/'run.json';record=rt.json.loads(path.read_text(encoding='utf-8'))
    record['native_settings']['max_iters']=20000000
    record['reference_policy']=(f'Separate fresh reference with a {a.seconds:g}-second search cap and '
        '20-million SCS iteration cap. Not an additional main-benchmark repetition. '
        'The single native solve emits its candidate only on return; intermediate certificates '
        'may be unavailable. The 1-hour and 6-hour references are independent executions, '
        'not two checkpoints of the same SCS internal state.')
    if record['status']=='numerical_failure' and 'reached time_limit_secs' in (a.output/'solver.log').read_text(encoding='utf-8'):
        record['status']='time_limit'
    rt.write_json(path,record)


if __name__=='__main__':main()
