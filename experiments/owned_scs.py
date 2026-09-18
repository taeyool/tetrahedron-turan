"""Invoke the isolated, memory-bounded SCS build without mapping A in Python."""
import os
from pathlib import Path
import subprocess
import numpy as np
import runtime as rt


def run(cache,matrix,metadata,b,c,output,budget,reserve,max_iters=20000000,variant='owned'):
    build=Path(cache)/'owned-scs-v4'
    manifest=rt.json.loads((build/'manifest.json').read_text())
    exe=build/f'scs-{variant}.exe'
    assert rt.digest(exe)==manifest['file_sha256'][exe.name]
    blas=Path(manifest['blas_path'])
    assert rt.digest(blas)==manifest['blas_sha256']
    # MinGW links the DLL's internal export name, whereas the wheel renames it.
    assert rt.digest(build/'openblas.dll')==manifest['blas_sha256']
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    m,n=metadata['shape'];cone=metadata['cone']
    assert len(b)==m and len(c)==n and budget>reserve>=0
    header=[m,n,metadata['nnz'],cone['z'],cone['l'],len(cone['s']),max_iters,budget,reserve]
    (output/'request.txt').write_text(' '.join(map(str,header))+'\n'+' '.join(map(str,cone['s']))+'\n')
    np.asarray(b,dtype='<f8').tofile(output/'b.f64')
    np.asarray(c,dtype='<f8').tofile(output/'c.f64')
    env=os.environ.copy()
    env['PATH']=str(blas.parent)+os.pathsep+'C:/Strawberry/c/bin'+os.pathsep+env.get('PATH','')
    env['OPENBLAS_NUM_THREADS']='1';env['OMP_NUM_THREADS']='1';env['MKL_NUM_THREADS']='1'
    with (output/'solver.log').open('w',encoding='utf-8') as stream:
        result=subprocess.run([str(exe),str(Path(matrix).resolve()),str(output.resolve())],
                              stdout=stream,stderr=subprocess.STDOUT,env=env)
    diagnostics_path=output/'info.json'
    diagnostics=rt.json.loads(diagnostics_path.read_text()) if diagnostics_path.exists() else {}
    rt.write_json(output/'invocation.json',dict(returncode=result.returncode,
        executable_sha256=rt.digest(exe),build_manifest_sha256=rt.digest(build/'manifest.json'),
        environment_threads={k:env[k] for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']},
        matrix_shape=metadata['shape'],matrix_nnz=metadata['nnz'],budget_seconds=budget,
        evaluation_reserve_seconds=reserve,variant=variant))
    if result.returncode or diagnostics.get('status_val') not in [1,2]:
        return dict(success=False,backend_status=diagnostics.get('status',f'owned_scs_exit_{result.returncode}'),
                    info=diagnostics)
    assert diagnostics['rho_x']==manifest['rho_x']==100.0
    values={name:np.fromfile(output/f'{name}.f64',dtype='<f8') for name in ['x','y','s']}
    assert len(values['x'])==n and len(values['y'])==len(values['s'])==m
    assert all(np.all(np.isfinite(a)) for a in values.values())
    return dict(success=True,info=diagnostics,**values)
