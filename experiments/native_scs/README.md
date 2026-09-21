# SCS inputs for the full seven-vertex SDPs

These are the source inputs of the final `owned-scs-v4` build used by the
recorded `M7-no5` and `M7-all5` `SDP-FULL` trials. The upstream SCS 3.2.8
source archive, its URL and SHA-256, the four local C files, and the upstream
MIT license are included. No prebuilt executable is required.

The local files transfer ownership of the sparse matrix buffers to SCS to
avoid an extra copy, reserve time for candidate evaluation at shutdown, and
add inner-CG timing diagnostics. The driver uses `rho_x=100`, the setting of
the final full-model runs. The stock and owned executables share this driver
and its settings; the stock variant uses the upstream solver implementation.
These files are preserved source versions, not a new solver algorithm.

From the repository root on Windows, with the pinned requirements and MinGW
GCC on PATH:

```sh
python experiments/build_native_scs.py --cache .research-repro/cache
python -X utf8 experiments/runtime.py experiments/validate_owned_scs.py --cache .research-repro/cache --output .research-repro/native-validation
```

The builder verifies all bundled inputs and the OpenBLAS DLL supplied by the
Windows SCS 3.2.8 wheel. It records the actual compiler, commands, source and
binary hashes in the new cache. Use a new cache if rebuilding. Binaries may
differ between compiler versions; the validation compares stock, owned and
wheel results on small SDPs and exercises deadline handling. Full-model
searches additionally need the feature and packed-matrix caches prepared by
`experiments/reproduce.py`.
