"""Bounded sequential pilots; never starts production by itself."""
import argparse
import datetime as dt
import os
from pathlib import Path
import sys
import time
import runtime as rt
from run_overnight import watch

ARMS=[('M6','SDP-FULL'),('M6','LP-CUT'),('M6','SDP-CG'),
      ('M6','LP-CUT-CG'),('M7-lift6','LP-CUT-CG')]

def main(base,deadline,label):
    state=dict(status='validating',pid=os.getpid(),deadline_epoch=deadline,completed=[],active=None)
    path=base/f'{label}-status.json'
    rt.write_json(path,state)
    if os.name=='nt':
        import ctypes
        ctypes.windll.kernel32.SetThreadExecutionState(0x80000001)
    try:
        validation=base/'validation'/label
        command=[sys.executable,'-X','utf8',str(rt.HERE/'remaining_models.py'),
            '--cache',str(base/'cache'),'--output',str(base/'validation/models.json')]
        result=watch(command,validation,min(deadline,time.time()+600),40*1024**3)
        assert result['returncode']==0,'Independent model validation failed'
        for model,method in ARMS:
            output=base/label/model/method
            state.update(status='pilot',active=f'{model}/{method}'); rt.write_json(path,state)
            command=[sys.executable,'-X','utf8',str(rt.HERE/'run_remaining_method.py'),
                '--model',model,'--method',method,'--cache',str(base/'cache'),
                '--output',str(output),'--seconds','300','--phase','pilot']
            result=watch(command,output,min(deadline,time.time()+1260),40*1024**3,search_limit=300)
            run=rt.json.loads((output/'run.json').read_text(encoding='utf-8'))
            assert result['returncode']==0 and run['status'] in ['completed','time_limit','numerical_failure'],(model,method,run['status'])
            assert run.get('best_global_upper') is not None,(model,method,'no completed candidate')
            state['completed'].append(dict(model=model,method=method,status=run['status'],
                upper=run['best_global_upper'],search_seconds=run['search_seconds']))
            rt.write_json(path,state)
        state.update(status='finished',active=None,finished_epoch=time.time())
    except Exception as exc:
        import traceback
        traceback.print_exc()
        state.update(status='failed',error=repr(exc),finished_epoch=time.time())
    finally:
        rt.write_json(path,state)
        if os.name=='nt':
            ctypes.windll.kernel32.SetThreadExecutionState(0x80000000)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--campaign',type=Path,required=True)
    p.add_argument('--deadline',required=True)
    p.add_argument('--label',default='pilot')
    a=p.parse_args()
    main(a.campaign.resolve(),dt.datetime.fromisoformat(a.deadline).timestamp(),a.label)
