#include <apps_sfdl_hw/fast_ram_test_p_exo.h>
#include <apps_sfdl_gen/fast_ram_test_cons.h>
#include <common/sha1.h>
#include <storage/configurable_block_store.h>

#pragma pack(push)
#pragma pack(1)

//This file will NOT be overwritten by the code generator, if it already
//exists. make clean will also not remove this file.

fast_ram_testProverExo::fast_ram_testProverExo() {

  //Uncomment and fix to specify the sizes of the input and output types
  //to baseline_minimal:
  //baseline_minimal_input_size = sizeof(something);
  //baseline_minimal_output_size = sizeof(something);

}

//using namespace fast_ram_test_cons;

void fast_ram_testProverExo::init_exo_inputs(
  const mpq_t* input_q, int num_inputs,
  char *folder_path, HashBlockStore *bs) {
  
}

void fast_ram_testProverExo::export_exo_inputs(
  const mpq_t* output_q, int num_outputs,
  char* folder_path, HashBlockStore *bs) {

}

void fast_ram_testProverExo::run_shuffle_phase(char *folder_path) {

}

void fast_ram_testProverExo::baseline_minimal(void* input, void* output){
  //Run the computation
}

struct In { uint16_t index; uint16_t array[4];};
struct Out { uint16_t output;};

void fast_ram_testProverExo::baseline(const mpq_t* input_q, int num_inputs, 
      mpq_t* output_recomputed, int num_outputs) {
  //struct In input;
  //struct Out output;
  // Fill code here to prepare input from input_q.

  // Call baseline_minimal to run the computation

  // Fill code here to dump output to output_recomputed.
  uint16_t index = mpz_get_ui(mpq_numref(input_q[0]));
  uint16_t i = index % 4;
  mpq_set_ui(output_recomputed[0], 0, 1);
  mpq_set(output_recomputed[1 + i], input_q[1 + i]);
  mpq_add(output_recomputed[1 + i], output_recomputed[1 + i], input_q[0]);
  mpq_set(output_recomputed[5 + 3 * i], input_q[5 + 3 * i]);
  mpq_set(output_recomputed[5 + 3 * i + 1], input_q[5 + 3 * i + 1]);
  mpq_set(output_recomputed[5 + 3 * i + 2], input_q[5 + 3 * i + 2]);

  mpq_add(output_recomputed[5 + 3 * i], output_recomputed[5 + 3 * i], input_q[0]);
  mpq_t temp;
  mpq_init(temp);
  mpq_mul(temp, input_q[i + 1], input_q[0]);
  mpq_add(output_recomputed[5 + 3 * i + 1], output_recomputed[5 + 3 * i + 1], temp);
  mpq_sub(output_recomputed[5 + 3 * i + 2], output_recomputed[5 + 3 * i + 2], input_q[0]);

  if (mpq_cmp_ui(input_q[0], 1000, 1) > 0) {
    mpq_set(output_recomputed[17], input_q[17]);
  } else {
    mpq_set(output_recomputed[17], input_q[18]);
  }

}

//Refer to apps_sfdl_gen/fast_ram_test_cons.h for constants to use in this exogenous
//check.
bool fast_ram_testProverExo::exogenous_check(const mpz_t* input, const mpq_t* input_q,
      int num_inputs, const mpz_t* output, const mpq_t* output_q, int num_outputs, mpz_t prime) {

  bool passed_test = true;
#ifdef ENABLE_EXOGENOUS_CHECKING
  //gmp_printf("<Exogenous check not implemented>");
  mpq_t *output_recomputed;
  alloc_init_vec(&output_recomputed, num_outputs);
  baseline(input_q, num_inputs, output_recomputed, num_outputs);

  for(int i = 0; i < num_outputs; i++){
    if (mpq_equal(output_recomputed[i], output_q[i]) == 0){
      passed_test = false;
      //break;
    }
    gmp_printf("expected: %Qd actual: %Qd\n", output_recomputed[i], output_q[i]);
  }
  clear_vec(num_outputs, output_recomputed);
#else
  gmp_printf("<Exogenous check disabled>\n");
#endif
  return passed_test;
};

#pragma pack(pop)
