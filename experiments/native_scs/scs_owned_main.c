/* File-based SCS 3.2.8 driver. The private build transfers ownership of A once. */
#include "scs.h"
#include "scs_work.h"
#include "util.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

static FILE *open_file(const char *dir, const char *name, const char *mode) {
  char path[8192];
  if (snprintf(path, sizeof(path), "%s/%s", dir, name) >= sizeof(path)) exit(20);
  FILE *f = fopen(path, mode);
  if (!f) { perror(path); exit(21); }
  return f;
}
static void read_array(const char *dir, const char *name, void *ptr, size_t size, size_t count) {
  FILE *f = open_file(dir, name, "rb");
  if (fread(ptr, size, count, f) != count || fgetc(f) != EOF) {
    fprintf(stderr, "Wrong array length: %s\n", name); exit(22);
  }
  fclose(f);
}
static void write_array(const char *dir, const char *name, void *ptr, size_t count) {
  FILE *f = open_file(dir, name, "wb");
  if (fwrite(ptr, sizeof(scs_float), count, f) != count) exit(23);
  fclose(f);
}
static void number(FILE *f, const char *key, double value) {
  fprintf(f, ",\n\"%s\":", key);
  if (isfinite(value)) fprintf(f, "%.17g", value); else fprintf(f, "null");
}
int main(int argc, char **argv) {
  if (argc != 3 || sizeof(scs_int) != 8 || sizeof(scs_float) != 8) return 2;
  setvbuf(stdout, NULL, _IONBF, 0);
  SCS(timer) timer; SCS(tic)(&timer);
  ScsData *data = calloc(1, sizeof(ScsData));
  ScsCone cone = {0}; ScsSettings settings; ScsSolution solution = {0}; ScsInfo info = {0};
  scs_int nnz; double budget, reserve;
  scs_set_default_settings(&settings);
  FILE *request = open_file(argv[2], "request.txt", "r");
  if (fscanf(request, "%lld %lld %lld %lld %lld %lld %lld %lf %lf",
      &data->m, &data->n, &nnz, &cone.z, &cone.l, &cone.ssize,
      &settings.max_iters, &budget, &reserve) != 9) return 3;
  if (data->m <= 0 || data->n <= 0 || nnz <= 0 || cone.ssize <= 0 || budget <= reserve) return 4;
  cone.s = calloc(cone.ssize, sizeof(scs_int));
  for (scs_int j=0; j<cone.ssize; ++j)
    if (fscanf(request, "%lld", &cone.s[j]) != 1 || cone.s[j] <= 0) return 5;
  fclose(request);
  data->A = calloc(1, sizeof(ScsMatrix));
  data->A->m = data->m; data->A->n = data->n;
  data->A->x = malloc(nnz * sizeof(scs_float));
  data->A->i = malloc(nnz * sizeof(scs_int));
  data->A->p = malloc((data->n+1) * sizeof(scs_int));
  data->b = malloc(data->m * sizeof(scs_float));
  data->c = malloc(data->n * sizeof(scs_float));
  if (!data->A->x || !data->A->i || !data->A->p || !data->b || !data->c) return 6;
  read_array(argv[1], "data.f64", data->A->x, sizeof(scs_float), nnz);
  read_array(argv[1], "indices.i64", data->A->i, sizeof(scs_int), nnz);
  read_array(argv[1], "indptr.i64", data->A->p, sizeof(scs_int), data->n+1);
  read_array(argv[2], "b.f64", data->b, sizeof(scs_float), data->m);
  read_array(argv[2], "c.f64", data->c, sizeof(scs_float), data->n);
  if (data->A->p[0] != 0 || data->A->p[data->n] != nnz) return 7;
  settings.eps_abs = settings.eps_rel = settings.eps_infeas = 1e-8;
  /* Pilot-frozen proximal scale; feasibility targets and mathematical data are unchanged. */
  settings.rho_x = 100.0;
  settings.normalize = 1; settings.acceleration_lookback = 10; settings.verbose = 1;
  settings.time_limit_secs = budget-reserve;
  double input_seconds = SCS(tocq)(&timer)/1000;
  printf("Input ready after %.6f seconds; SCS %s; matrix ownership driver\n", input_seconds, scs_version());
  ScsWork *work = scs_init(data, &cone, &settings);
  if (!work) return 8;
  scs_int m = data->m, n = data->n;
  SCS(free_data)(data); free(cone.s);
  double assembly_seconds = SCS(tocq)(&timer)/1000;
  double cap = budget - assembly_seconds - reserve;
  if (cap <= 0) { scs_finish(work); return 9; }
  work->stgs->time_limit_secs = cap;
  printf("Setup ready after %.6f seconds; remaining solve cap %.6f seconds\n", assembly_seconds, cap);
  scs_int status = scs_solve(work, &solution, &info, 0);
  FILE *diagnostics = open_file(argv[2], "info.json", "w");
  fprintf(diagnostics, "{\n\"status_val\":%lld,\n\"status\":\"%s\",\n\"version\":\"%s\",\n\"iter\":%lld",
      status, info.status, scs_version(), info.iter);
  number(diagnostics, "rho_x", settings.rho_x);
  number(diagnostics, "pobj", info.pobj); number(diagnostics, "dobj", info.dobj);
  number(diagnostics, "res_pri", info.res_pri); number(diagnostics, "res_dual", info.res_dual);
  number(diagnostics, "gap", info.gap); number(diagnostics, "res_infeas", info.res_infeas);
  number(diagnostics, "res_unbdd_a", info.res_unbdd_a); number(diagnostics, "res_unbdd_p", info.res_unbdd_p);
  number(diagnostics, "setup_time", info.setup_time); number(diagnostics, "solve_time", info.solve_time);
  number(diagnostics, "lin_sys_time", info.lin_sys_time); number(diagnostics, "cone_time", info.cone_time);
  number(diagnostics, "accel_time", info.accel_time); number(diagnostics, "scale", info.scale);
  number(diagnostics, "input_seconds", input_seconds); number(diagnostics, "assembly_seconds", assembly_seconds);
  number(diagnostics, "actual_time_limit_setting_seconds", cap);
  fprintf(diagnostics, "\n}\n"); fclose(diagnostics);
  if (status == 1 || status == 2) {
    write_array(argv[2], "x.f64", solution.x, n);
    write_array(argv[2], "y.f64", solution.y, m);
    write_array(argv[2], "s.f64", solution.s, m);
  }
  free(solution.x); free(solution.y); free(solution.s); scs_finish(work);
  return (status == 1 || status == 2) ? 0 : 10;
}
