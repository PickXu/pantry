#include <common/measurement.h>
#include <common/utility.h>
#include <include/avl_tree.h>
#include <storage/configurable_block_store.h>
#include <storage/db_util.h>
#include <storage/exo.h>

#define MAX_TREE_LEVEL 7
#define NUM_OF_SUBTREE (1 << MAX_TREE_LEVEL)

#define NUM_OF_CHUNKS 128

int main(int argc, char **argv) {
  int size = atoi(argv[1]);
  assert(system("rm -rf " FOLDER_STATE) == 0);
  Student_handle_t handle = create_db(size - 1, NUM_OF_CHUNKS, MAX_TREE_LEVEL, "prover_1_default_shared_db", FOLDER_STATE);
  mpq_t* input_q;
  int num_inputs = sizeof(Student_handle_t) / sizeof(uint64_t);
  alloc_init_vec(&input_q, num_inputs);

  uint64_t* input_ptr = (uint64_t*)&handle;
  for(int i = 0; i < num_inputs; i++) {
    mpq_set_ui(input_q[i], input_ptr[i], 1);
  }

  recursive_mkdir(FOLDER_PERSIST_STATE, S_IRWXU);
  dump_vector(num_inputs, input_q, "db_handle", FOLDER_PERSIST_STATE);
  return 0;
}
