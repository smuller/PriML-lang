
#include<stdio.h>
#include<stdlib.h>
#include<z3.h>

typedef struct Z3ML {
  Z3_context ctx;
  Z3_solver s;
  Z3_func_decl le;
  Z3_sort prio;
} Z3ML ;

// From: https://github.com/Z3Prover/z3/blob/master/examples/c/test_capi.c
//void error_handler(Z3_context c, Z3_error_code e)
//{
//    printf("Error code: %d\n", e);
//    exitf("incorrect use of Z3");
//}

Z3ML *Z3ML_make_context_and_solver () {
  Z3ML *z3 = malloc(sizeof(Z3ML));
  Z3_config cfg = Z3_mk_config();
  z3->ctx = Z3_mk_context(cfg);
  z3->s = Z3_mk_solver(z3->ctx);
  Z3_solver_push(z3->ctx, z3->s);
  z3->prio = Z3_mk_uninterpreted_sort (z3->ctx, Z3_mk_string_symbol (z3->ctx, "Prio"));
  z3->le = Z3_mk_partial_order(z3->ctx, z3->prio, 0);
  return z3;
}

Z3_ast *Z3ML_add_constant (Z3ML *z3, const char *c) {
  Z3_ast *p = malloc(sizeof(Z3_ast));
  *p = Z3_mk_const (z3->ctx, Z3_mk_string_symbol (z3->ctx, c), z3->prio);
  return p;
}

void *Z3ML_add_distinct (Z3ML *z3, const Z3_ast **prios, int n) {
  printf("Allocating ast array\n");
  Z3_ast *asts = malloc(sizeof(Z3_ast) * n);
  for (int i = 0; i < n; i++) {
    printf("0x%x\n", prios[i]);
    asts[i] = *(prios[i]);
  }
  printf("Built asts array\n");
  Z3_solver_assert(z3->ctx, z3->s, Z3_mk_distinct (z3->ctx, n, asts));
  printf("called z3\n");
  free(asts);
  printf("done\n");
}

void *Z3ML_add_one_of (Z3ML *z3, Z3_ast *var, Z3_ast **consts, int n) {
  Z3_ast *apps = malloc(sizeof(Z3_ast) * n);
  for (int i = 0; i < n; i++) {
    apps[i] = Z3_mk_eq(z3->ctx, *var, *(consts[i]));
  }
  Z3_solver_assert(z3->ctx, z3->s, Z3_mk_or(z3->ctx, n, apps));
  free(apps);
}

void Z3ML_add_constraint (Z3ML* z3, Z3_ast *p1, Z3_ast *p2) {
  Z3_ast args[2] = {*p1, *p2};
  Z3_ast app = Z3_mk_app(z3->ctx, z3->le, 2, args);
  Z3_solver_assert(z3->ctx, z3->s, app);
}

void Z3ML_add_negated_constraint (Z3ML* z3, Z3_ast *p1, Z3_ast *p2) {
  Z3_ast args[2] = {*p1, *p2};
  Z3_ast app = Z3_mk_app(z3->ctx, z3->le, 2, args);
  Z3_solver_assert(z3->ctx, z3->s, Z3_mk_not(z3->ctx, app));
}

void Z3ML_add_negate_and_constraints (Z3ML *z3, Z3_ast **args, int n) {
  Z3_ast *apps = malloc(sizeof(Z3_ast) * n / 2);
  for (int i = 0; i < n; i += 2) {
    Z3_ast app_args[2] = {*(args[i]), *(args[i + 1])};
    apps[i / 2] = Z3_mk_app(z3->ctx, z3->le, 2, app_args);
  }
  Z3_solver_assert(z3->ctx, z3->s, Z3_mk_not(z3->ctx, Z3_mk_and(z3->ctx, n / 2, apps)));
  free(apps);
}

bool Z3ML_check (Z3ML *z3) {
  printf("checking: %s\n", Z3_solver_to_string(z3->ctx, z3->s));
  switch (Z3_solver_check(z3->ctx, z3->s)) {
  case Z3_L_FALSE:
    Z3_solver_dec_ref(z3->ctx, z3->s);
    Z3_del_context(z3->ctx);
    free(z3);
    printf("Z3 unsat\n");
    return false;
  case Z3_L_TRUE:
  case Z3_L_UNDEF:
    Z3_solver_dec_ref(z3->ctx, z3->s);
    Z3_del_context(z3->ctx);
    free(z3);
    printf("Z3 sat\n");
    return true;
  }
  Z3_solver_dec_ref(z3->ctx, z3->s);
  Z3_del_context(z3->ctx);
  free(z3);
  return true;
}
    
bool Z3ML_check_string (const char *str) {
  Z3_config cfg = Z3_mk_config();
  Z3_context ctx = Z3_mk_context(cfg);
  Z3_solver s = Z3_mk_solver(ctx);
  Z3_solver_from_string(ctx, s, str);
  switch (Z3_solver_check(ctx, s)) {
  case Z3_L_FALSE:
    Z3_solver_dec_ref(ctx, s);
    Z3_del_context(ctx);
    //printf("Z3 unsat\n");
    return false;
  case Z3_L_TRUE:
  case Z3_L_UNDEF:
    Z3_solver_dec_ref(ctx, s);
    Z3_del_context(ctx);
    //printf("Z3 sat\n");
    return true;
  }
  Z3_solver_dec_ref(ctx, s);
  Z3_del_context(ctx);
    
  return true;
}
    
