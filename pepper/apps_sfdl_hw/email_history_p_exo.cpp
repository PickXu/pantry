#include <apps_sfdl_hw/email_history_p_exo.h>
#include <apps_sfdl_gen/email_history_cons.h>
#include <common/sha1.h>
#include <storage/configurable_block_store.h>

#pragma pack(push)
#pragma pack(1)

//This file will NOT be overwritten by the code generator, if it already
//exists. make clean will also not remove this file.

email_historyProverExo::email_historyProverExo() { }

using namespace email_history_cons;

void email_historyProverExo::init_exo_inputs(
  const mpq_t* input_q, int num_inputs,
  char *folder_path, HashBlockStore *bs) {
}

void email_historyProverExo::export_exo_inputs(
  const mpq_t* output_q, int num_outputs,
  char* folder_path, HashBlockStore *bs) {

}

void email_historyProverExo::run_shuffle_phase(char *folder_path) {

}

void email_historyProverExo::baseline(const mpq_t* input_q, int num_inputs, 
      mpq_t* output_recomputed, int num_outputs) {
  //struct In input;
  //struct Out output;
  // Fill code here to prepare input from input_q.
  
  // Do the computation

  // Fill code here to dump output to output_recomputed.
}

//Refer to apps_sfdl_gen/email_history_cons.h for constants to use in this exogenous
//check.
bool email_historyProverExo::exogenous_check(const mpz_t* input, const mpq_t* input_q,
      int num_inputs, const mpz_t* output, const mpq_t* output_q, int num_outputs, mpz_t prime) {

  bool passed_test = true;
#ifdef ENABLE_EXOGENOUS_CHECKING
  gmp_printf("<Exogenous check not implemented>");
  /*mpq_t *output_recomputed;
  alloc_init_vec(&output_recomputed, num_outputs);
  baseline(input_q, num_inputs, output_recomputed, num_outputs);

  for(int i = 0; i < num_outputs; i++){
    if (mpq_equal(output_recomputed[i], output_q[i]) == 0){
      passed_test = false;
      break;
    }
  }
  clear_vec(num_outputs, output_recomputed);*/
#else
  gmp_printf("<Exogenous check disabled>\n");
#endif
  return passed_test;
};

#pragma pack(pop)
