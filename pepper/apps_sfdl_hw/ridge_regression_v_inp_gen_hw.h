#ifndef APPS_SFDL_HW_V_INP_GEN_HW_H_
#define APPS_SFDL_HW_V_INP_GEN_HW_H_

#include <libv/libv.h>
#include <common/utility.h>
#include <apps_sfdl_gen/ridge_regression_v_inp_gen.h>
#include <apps_sfdl_gen/ridge_regression_cons.h>
#pragma pack(push)
#pragma pack(1)

/*
* Provides the ability for user-defined input creation
*/
class ridge_regressionVerifierInpGenHw : public InputCreator {
  public:
    ridge_regressionVerifierInpGenHw(Venezia* v);

    void create_input(mpq_t* input_q, int num_inputs);
  private:
    Venezia* v;
    ridge_regressionVerifierInpGen compiler_implementation;

};
#pragma pack(pop)
#endif  // APPS_SFDL_HW_V_INP_GEN_HW_H_
