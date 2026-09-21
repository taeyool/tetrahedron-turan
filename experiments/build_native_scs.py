"""Build the pinned Windows SCS 3.2.8 executables used by the full M7 arms."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
SOURCES = HERE / "native_scs"

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def build(cache, compiler):
    if os.name != "nt":
        raise SystemExit("The recorded native SCS build requires Windows and MinGW GCC.")
    spec = json.loads((SOURCES / "source-manifest.json").read_text(encoding="utf-8"))
    for name, expected in spec["sha256"].items():
        if digest(SOURCES / name) != expected:
            raise ValueError(f"Native source hash mismatch: {name}")
    target = cache.resolve() / "owned-scs-v4"
    if target.exists():
        raise FileExistsError(f"Use a new cache directory; retaining prior build: {target}")
    compiler = shutil.which(compiler)
    if not compiler:
        raise FileNotFoundError("MinGW gcc must be on PATH, or pass --compiler.")
    scs = importlib.util.find_spec("scs")
    if scs is None:
        raise ImportError("Install requirements.txt, including the SCS 3.2.8 wheel.")
    libraries = Path(scs.origin).parent.parent / "scs.libs"
    dlls = list(libraries.glob("openblas*.dll"))
    if len(dlls) != 1:
        raise FileNotFoundError(f"Expected one OpenBLAS DLL from the SCS wheel in {libraries}")
    blas = dlls[0].resolve()
    if digest(blas) != spec["historical_blas_sha256"]:
        raise ValueError("OpenBLAS DLL differs from the recorded Windows SCS 3.2.8 wheel.")
    target.mkdir(parents=True)
    archive = SOURCES / spec["source_archive"]["filename"]
    with tarfile.open(archive) as tar:
        # The archive is hash-pinned; still reject escaping paths and links.
        for member in tar.getmembers():
            resolved = (target / member.name).resolve()
            if target not in resolved.parents or member.issym() or member.islnk():
                raise ValueError(f"Unsafe archive entry: {member.name}")
        tar.extractall(target)
    source = target / "scs-3.2.8/scs_source"
    shutil.copyfile(blas, target / "openblas.dll")
    common = [str(source / "src" / (name + ".c"))
              for name in ["aa","cones","ctrlc","exp_cone","linalg","normalize","rw","scs_version"]]
    common += [str(source / "linsys" / (name + ".c")) for name in ["scs_matrix","csparse"]]
    commands = {}
    for variant in ["stock", "owned"]:
        extra = ([source/"linsys/cpu/indirect/private.c", SOURCES/"scs_owned_main.c",
                  source/"src/util.c", source/"src/scs.c"] if variant == "stock" else
                 [SOURCES/"private_diagnostic.c", SOURCES/"scs_owned_main.c",
                  SOURCES/"util_owned.c", SOURCES/"scs_timed.c"])
        command = [compiler] + spec["compiler_flags"]
        command += ["-I"+str(source/x) for x in ["include","linsys","linsys/cpu/indirect"]]
        command += common + list(map(str, extra)) + [str(blas), "-lm", "-o", str(target/f"scs-{variant}.exe")]
        result = subprocess.run(command, capture_output=True, text=True)
        (target/f"{variant}.build.log").write_text(result.stdout+result.stderr, encoding="utf-8")
        result.check_returncode()
        commands[variant] = command
    manifest = dict(build_id="owned-scs-v4", scs_version="3.2.8", rho_x=100.0,
                    compiler=subprocess.check_output([compiler,"--version"],text=True).splitlines()[0],
                    compiler_directory=str(Path(compiler).parent), compiler_flags=spec["compiler_flags"],
                    source_manifest_sha256=digest(SOURCES/"source-manifest.json"),
                    blas_path=str(blas), blas_sha256=digest(blas), commands=commands,
                    file_sha256={f"scs-{v}.exe":digest(target/f"scs-{v}.exe") for v in ["stock","owned"]},
                    validation="Build only; run validate_owned_scs.py before numerical use.")
    (target/"manifest.json").write_text(json.dumps(manifest,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(dict(status="built",manifest=str(target/"manifest.json"))))

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache",type=Path,required=True)
    parser.add_argument("--compiler",default="gcc")
    args = parser.parse_args()
    build(args.cache,args.compiler)
