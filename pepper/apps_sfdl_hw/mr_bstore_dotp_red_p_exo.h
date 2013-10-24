#ifndef APPS_SFDL_GEN_MR_BSTORE_DOTP_RED_P_EXO_H_
#define APPS_SFDL_GEN_MR_BSTORE_DOTP_RED_P_EXO_H_

#include <apps_sfdl_gen/mr_bstore_dotp_red_p.h>
#include <apps_sfdl_hw/mr_bstore_dotp_red_v_inp_gen_hw.h>

//Comment out line to disable exogenous checking for this computation.
#define ENABLE_EXOGENOUS_CHECKING

/*
* Overrides the exogenous check method of ComputationProver.
*/
class mr_bstore_dotp_redProverExo : public ExogenousChecker {
  public:
    mr_bstore_dotp_redProverExo();

    bool exogenous_check(const mpz_t* input, const mpq_t* input_q,
      int num_inputs, const mpz_t* output, const mpq_t* output_q, int num_outputs, mpz_t prime);
    void baseline_minimal(void* input, void* output);
    void baseline(const mpq_t* input_q, int num_inputs, 
      mpq_t* output_recomputed, int num_outputs);
    void init_exo_inputs(const mpq_t*, int, char*, HashBlockStore*);
    void export_exo_inputs(const mpq_t*, int, char*, HashBlockStore*);
    void run_shuffle_phase(char *folder_path); 
};
#endif  // APPS_SFDL_GEN_MR_BSTORE_DOTP_RED_P_EXO_H_
