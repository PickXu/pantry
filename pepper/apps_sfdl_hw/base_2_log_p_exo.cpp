#include <apps_sfdl_hw/base_2_log_p_exo.h>
#include <apps_sfdl_gen/base_2_log_cons.h>
#include <common/sha1.h>
#include <storage/configurable_block_store.h>
#include <cmath>

#pragma pack(push)
#pragma pack(1)

//This file will NOT be overwritten by the code generator, if it already
//exists. make clean will also not remove this file.

base_2_logProverExo::base_2_logProverExo() { }

using namespace base_2_log_cons;

void base_2_logProverExo::init_exo_inputs(
  const mpq_t* input_q, int num_inputs,
  char *folder_path, HashBlockStore *bs) {
  
}

void base_2_logProverExo::export_exo_inputs(
  const mpq_t* output_q, int num_outputs,
  char* folder_path, HashBlockStore *bs) {

}

void base_2_logProverExo::run_shuffle_phase(char *folder_path) {

}

#include "apps_sfdl/base_2_log.c"

void base_2_logProverExo::baseline(const mpq_t* input_q, int num_inputs, 
      mpq_t* output_recomputed, int num_outputs) {
  //struct In input;
  //struct Out output;
  // Fill code here to prepare input from input_q.
  
  // Do the computation
  uint32_t a = mpz_get_ui(mpq_numref(input_q[0]));

  uint32_t log2a = (uint32_t)log2(a);
  uint32_t clog2a = uintlog2(a);
  //gmp_printf("%d %d\n", log2a, clog2a);
  assert(log2a == clog2a);

  // Fill code here to dump output to output_recomputed.
  mpq_set_ui(output_recomputed[0], 0, 1);
  mpq_set_ui(output_recomputed[1], log2a, 1);
}

//Refer to apps_sfdl_gen/base_2_log_cons.h for constants to use in this exogenous
//check.
bool base_2_logProverExo::exogenous_check(const mpz_t* input, const mpq_t* input_q,
      int num_inputs, const mpz_t* output, const mpq_t* output_q, int num_outputs, mpz_t prime) {

  bool passed_test = true;
#ifdef ENABLE_EXOGENOUS_CHECKING
  mpq_t *output_recomputed;
  alloc_init_vec(&output_recomputed, num_outputs);
  baseline(input_q, num_inputs, output_recomputed, num_outputs);

  for(int i = 0; i < num_outputs; i++){
    if (mpq_equal(output_recomputed[i], output_q[i]) == 0){
      passed_test = false;
      break;
    }
  }
  clear_vec(num_outputs, output_recomputed);
#else
  gmp_printf("<Exogenous check disabled>\n");
#endif
  return passed_test;
};

#pragma pack(pop)
