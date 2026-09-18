#!/usr/bin/env python3
"""Verify an order-7 flag-algebra certificate for K4^(3) in the original schema.

This verifier handles certificates whose blocks have at most four roots
(the earlier certificates in legacy/). The main certificate of this
repository also has five-root blocks; verify it with
search/exactify_five_root.py --certificate certificate/K4_turan_order7_certificate.json.

Default use:
    python verify_K4_turan_order7_certificate.py

The program rebuilds all integer Gram corrections from the JSON certificate,
compiles the included exhaustive C++ oracle, and checks all 13,051,375
admissible labeled seven-vertex one-point extensions.
"""
from __future__ import annotations
import argparse, hashlib, json, math, shutil, struct, subprocess, sys, tempfile
from fractions import Fraction
from pathlib import Path
import numpy as np

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import flag_sdp_hyper3 as fs
from portable_raw_oracle import portable_ordered_source


def stat_numerators(H:list[int])->np.ndarray:
    ix=fs.edge_index(6); out=[]
    for mask in H:
        n1=n2=0
        for root in range(6):
            rem=[v for v in range(6) if v!=root]
            for a in range(5):
                for b in range(a+1,5):
                    u,v=rem[a],rem[b]
                    if not ((mask>>ix[tuple(sorted((root,u,v)))])&1):
                        continue
                    rest=[z for z in rem if z not in (u,v)]
                    if (mask>>ix[tuple(sorted(rest))])&1:
                        n1+=1
                    for i in range(3):
                        for j in range(i+1,3):
                            if (mask>>ix[tuple(sorted((root,rest[i],rest[j])))])&1:
                                n2+=1
        out.append(3*n1-n2)
    return np.asarray(out,dtype=np.int64)


def gram(factors:list[list[int]],dimension:int)->np.ndarray:
    if not factors:
        return np.zeros((dimension,dimension),dtype=np.int64)
    F=np.asarray(factors,dtype=np.int64)
    if F.ndim!=2 or F.shape[1]!=dimension:
        raise AssertionError(f'bad factor shape {F.shape}, expected (*,{dimension})')
    return F.T@F


def rebuild_candidate(cert:dict,path:Path)->None:
    D=int(cert['scale'])
    families=cert['order6_factors_by_block']+[cert[k] for k in (
        'order7_s1_factors','order7_s3_nonedge_factors','order7_s3_edge_factors')]
    assert type(cert['scale']) is int and type(cert['stationarity']['tau_numerator']) is int
    assert len(families)==12
    for rows,dimension in zip(families,[2,2,11,8,7,64,56,50,45,7,236,191]):
        assert all(len(row)==dimension and all(type(v) is int for v in row) for row in rows), 'Expected integer factor rows of the recorded dimension'
    assert sum(map(len,families))==cert['total_integer_square_factors']
    bounds=[sum(max(map(abs,row),default=0)**2 for row in rows) for rows in families]
    tau_num=int(cert['stationarity']['tau_numerator'])
    assert D>0 and int(cert['stationarity']['tau_denominator'])==D*D
    assert len(families)==12 and all(b<2**63 for b in bounds), 'Gram arithmetic may overflow int64'
    assert 720*(D*D+sum(bounds[:9]))+abs(tau_num)*720*12<2**63, 'Six-vertex arithmetic may overflow int64'
    H=[int(x) for x in cert['H_representatives']]
    blocks=fs.build_blocks(6,H,verbose=False)
    recorded=cert['order6_blocks']
    if len(blocks)!=len(recorded):
        raise AssertionError('order-6 block count mismatch')
    for block,meta in zip(blocks,recorded):
        actual=(block.s,block.l,block.sigma,len(block.flags),block.denominator,block.flags)
        expected=(int(meta['s']),int(meta['l']),int(meta['sigma']),int(meta['dimension']),int(meta['denominator']),[int(x) for x in meta['flags']])
        if actual!=expected:
            raise AssertionError('order-6 block metadata mismatch')

    class_num=np.asarray([bin(int(mask)).count('1')*36*D*D for mask in H],dtype=np.int64)
    factors_by_block=cert['order6_factors_by_block']
    if len(factors_by_block)!=len(blocks):
        raise AssertionError('order-6 factor block count mismatch')
    for block,factors in zip(blocks,factors_by_block):
        ratio=720//block.denominator
        for factor in factors:
            a=np.asarray(factor,dtype=np.int64)
            values=np.einsum('i,hij,j->h',a,block.counts.astype(np.int64),a,optimize=True)
            class_num += values*ratio

    tau_num=int(cert['stationarity']['tau_numerator'])
    class_num += tau_num*stat_numerators(H)*12

    Q1=gram(cert['order7_s1_factors'],7)
    Q0=gram(cert['order7_s3_nonedge_factors'],236)
    QE=gram(cert['order7_s3_edge_factors'],191)
    q1upper=[]
    for i in range(7):
        for j in range(i,7):
            q1upper.append(int(Q1[i,j]))

    with path.open('wb') as handle:
        handle.write(struct.pack('<QqIII',D,tau_num,len(H),236,191))
        np.asarray(class_num,dtype='<i8').tofile(handle)
        np.asarray(q1upper,dtype='<i8').tofile(handle)
        np.asarray(Q0,dtype='<i8').ravel().tofile(handle)
        np.asarray(QE,dtype='<i8').ravel().tofile(handle)


def parse_result(path:Path)->dict[str,str]:
    output={}
    for line in path.read_text().splitlines():
        parts=line.split()
        if parts:
            output[parts[0]]=' '.join(parts[1:])
    return output


def main()->None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--certificate',type=Path,default=HERE/'legacy/K4_turan_order7_exact_certificate.json')
    parser.add_argument('--threads',type=int,default=max(1,min(8,(__import__('os').cpu_count() or 1))))
    parser.add_argument('--keep-temp',action='store_true')
    parser.add_argument('--portable',action='store_true',help='Use C++17 threads and portable bit extraction (ARM/macOS supported)')
    parser.add_argument('--report',type=Path,help='Write a verification report including the input certificate hash')
    args=parser.parse_args()

    certificate_bytes=args.certificate.read_bytes()
    cert=json.loads(certificate_bytes)
    H=[int(x) for x in cert['H_representatives']]
    if len(H)!=964 or H!=sorted(set(H)):
        raise AssertionError('expected 964 sorted, distinct six-vertex representatives')
    if not all(fs.is_k4free(mask,6) for mask in H):
        raise AssertionError('a six-vertex representative contains K4^(3)')
    all_reps=[int(x) for x in (HERE/'h6_all_reps.txt').read_text().split()]
    if all_reps!=sorted(set(all_reps)):
        raise AssertionError('full six-vertex representative list is not sorted/unique')
    lookup={mask:i for i,mask in enumerate(all_reps)}
    support_ids=[lookup[mask] for mask in H]
    expected_support=[i for i,mask in enumerate(all_reps) if fs.is_k4free(mask,6)]
    if support_ids!=expected_support:
        raise AssertionError('K4-free support list is incomplete or misordered')

    tmp_obj=tempfile.TemporaryDirectory(prefix='verify_k4_order7_')
    tmp=Path(tmp_obj.name)
    candidate=tmp/'candidate.bin'; support=tmp/'support_ids.txt'; result=tmp/'result.txt'; exe=tmp/'oracle'
    support.write_text('\n'.join(map(str,support_ids))+'\n')

    print('[1/5] Rebuilding exact integer Gram matrices ...',flush=True)
    rebuild_candidate(cert,candidate)
    included=HERE/'K4_turan_order7_exact_candidate.bin'
    if args.certificate.resolve()==(HERE/'legacy/K4_turan_order7_exact_certificate.json').resolve() and included.exists() and included.read_bytes()!=candidate.read_bytes():
        raise AssertionError('rebuilt candidate binary differs from included binary')
    print(f"[1/5] Integer square factors: {cert['total_integer_square_factors']}",flush=True)

    print('[2/5] Compiling exhaustive seven-vertex oracle ...',flush=True)
    oracle_source=HERE/'exact_certificate_raw_oracle.cpp'
    compiler=['g++','-O3','-std=c++17','-march=native','-mbmi2','-fopenmp']
    if args.portable:
        oracle_source=tmp/'portable_oracle.cpp'
        oracle_source.write_text(portable_ordered_source((HERE/'exact_certificate_raw_oracle.cpp').read_text()))
        compiler=['c++','-O3','-std=c++17','-pthread']
    subprocess.run(compiler+[str(oracle_source),'-o',str(exe)],check=True)

    print('[3/5] Enumerating all admissible labeled seven-vertex extensions ...',flush=True)
    subprocess.run([
        str(exe),str(HERE/'h6_all_reps.txt'),str(support),str(candidate),str(result),str(args.threads)
    ],check=True)
    found=parse_result(result)

    raw_count=int(found['raw_count']); numerator=int(found['max_numerator']); denominator=int(found['denominator']); mask=int(found['max_mask'])
    if raw_count!=int(cert['raw_labeled_extensions_checked']):
        raise AssertionError(f'raw count mismatch: {raw_count}')
    if numerator!=int(cert['bound_numerator_unreduced']) or denominator!=int(cert['common_denominator_unreduced']):
        raise AssertionError('exact maximum coefficient mismatch')
    print(f'[3/5] Raw columns checked: {raw_count}',flush=True)

    print('[4/5] Checking exact rational comparison ...',flush=True)
    bound=Fraction(numerator,denominator)
    if bound!=Fraction(cert['bound_fraction']):
        raise AssertionError('reduced fraction mismatch')
    comparison=Fraction(cert['comparison_fraction'])
    if not bound<comparison:
        raise AssertionError('certificate does not improve the comparison value')
    if comparison-bound!=Fraction(cert['gap_below_comparison_fraction']):
        raise AssertionError('comparison gap mismatch')

    print('[5/5] PASS: exact certificate verified.',flush=True)
    print(f'Exact bound: {bound}')
    print(f'Decimal bound: {float(bound):.15f}')
    print(f'Gap below {comparison}: {comparison-bound} = {float(comparison-bound):.15f}')
    print(f'One maximizing raw mask found in this run: {mask}')

    if args.report:
        report={'status':'PASS','certificate':str(args.certificate),
                'certificate_sha256':hashlib.sha256(certificate_bytes).hexdigest(),
                'oracle_source_sha256':hashlib.sha256(oracle_source.read_bytes()).hexdigest(),
                'portable':args.portable,'raw_count':raw_count,'bound_fraction':str(bound),
                'maximizing_raw_mask':mask}
        args.report.parent.mkdir(parents=True,exist_ok=True)
        args.report.write_text(json.dumps(report,indent=2)+'\n')

    if args.keep_temp:
        destination=HERE/'verification_temp'
        if destination.exists():shutil.rmtree(destination)
        shutil.copytree(tmp,destination)
        print(f'Temporary verification files copied to {destination}')
    tmp_obj.cleanup()

if __name__=='__main__':
    main()
