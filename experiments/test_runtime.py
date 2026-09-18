"""Exercise real deadline termination of a child plus grandchild process."""
import argparse
from pathlib import Path
import sys
import time

import runtime as rt
import psutil
from run_overnight import watch


def main(output):
    child = ('import subprocess,sys,time; '
             'p=subprocess.Popen([sys.executable,"-c","import time; time.sleep(30)"]); '
             'print(p.pid,flush=True); time.sleep(30)')
    result=watch([sys.executable,'-c',child],output,time.time()+3,1024**3)
    assert result['status']=='campaign_time_limit' and result['elapsed_seconds']<10
    grandchild=int((output/'process.log').read_text().strip())
    assert not psutil.pid_exists(grandchild), 'watchdog left a grandchild running'
    rt.write_json(output/'test.json',dict(passed=True,grandchild_terminated=True,
        elapsed_seconds=result['elapsed_seconds'],kernel_job_limit_enforced=result['kernel_job_limit_enforced']))
    print('Watchdog killed the complete process tree within its deadline.',flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    main(parser.parse_args().output)
