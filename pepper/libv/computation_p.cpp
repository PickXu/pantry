#include <libv/zcomputation_p.h>
#include <storage/configurable_block_store.h>
#include <storage/gghA.h>
#include <storage/ram_impl.h>
#include <string>
#include <include/db.h>

ComputationProver::
ComputationProver(int ph, int b_size, int num_r, int size_input,
    const char *name_prover) : Prover(ph, b_size, num_r, size_input, name_prover) {
}

ComputationProver::
ComputationProver(int ph, int b_size, int num_r, int size_input,
    const char *name_prover, const char *_shared_bstore_file_name):
  Prover(ph, b_size, num_r, size_input, name_prover),
  shared_bstore_file_name(string(_shared_bstore_file_name)) {
}

ComputationProver::~ComputationProver() {
  if (_ram != NULL)
    delete _ram;
  if (_blockStore != NULL)
    delete _blockStore;
}

static void zcomp_assert(const char* a, const char* b,
    const char* error) {
  if (strcmp(a, b) != 0) {
    gmp_printf("%s, Expected : %s Actual: %s\n", error, b, a);
  }
}

static int try_next_token(FILE* fp, char* token) {
  return fscanf(FCGI_ToFILE(fp), "%s", token);
}

static void next_token_or_error(FILE* fp, char* token) {
  int ret = fscanf(FCGI_ToFILE(fp), "%s", token);
  if (ret != 1) {
    gmp_printf("Error reading from PWS file.\n");
  }
}

static void expect_next_token(FILE* fp, const char* expected, const char* error) {
  char buf[BUFLEN];
  next_token_or_error(fp, buf);
  zcomp_assert(buf, expected, error);
}

void ComputationProver::init_block_store() {
  snprintf(bstore_file_path, BUFLEN - 1, "%s/block_stores", FOLDER_STATE);
  mkdir(bstore_file_path, S_IRWXU);

  // the name of the block store is shared between the verifier and the prover.
  char bstore_file_path_priv[BUFLEN];
  snprintf(bstore_file_path_priv, BUFLEN - 1, "%s/prover_%d_%s", bstore_file_path, rank, shared_bstore_file_name.c_str());
  string bstore_file_path_priv_str(bstore_file_path_priv);
  _blockStore = new ConfigurableBlockStore(bstore_file_path_priv_str);

  _ram = new RAMImpl(_blockStore);
  exogenous_checker->set_block_store(_blockStore, _ram);
}

void ComputationProver::compute_poly(FILE* pws_file, int tempNum) {

  mpq_t& polyTarget = temp_qs[tempNum];
  mpq_t& termTarget = temp_qs[tempNum+1];
  mpq_set_ui(polyTarget, 0, 1);
  if (tempNum >= temp_stack_size-1) {
    gmp_printf("ERROR IN PROVER - Polynomial required more than %d recursive calls \n", temp_stack_size);
    return;
  }

  bool hasTerms = false;
  bool hasFactors = false;
  bool isEmpty = true;
  bool negate = false;

  char tok[BUFLEN], cmds[BUFLEN];
  while(try_next_token(pws_file, tok) != EOF) {
    //Emit last term, if necessary:
    if (strcmp(tok, "+") == 0 || strcmp(tok, "-") == 0) {
      if (hasFactors) {
        if (negate) {
          mpq_neg(termTarget, termTarget);
        }
        if (!hasTerms) {
          mpq_set(polyTarget, termTarget);
        } else {
          mpq_add(polyTarget, polyTarget, termTarget);
        }
        hasTerms = true;
        isEmpty = false;
        hasFactors = false;
        negate = false;
      }
    }

    if (strcmp(tok, "(") == 0) {
      //Recurse
      compute_poly(pws_file, tempNum + 2);
      mpq_t& subresult = temp_qs[tempNum + 2];
      if (!hasFactors) {
        mpq_set(termTarget, subresult);
      } else {
        mpq_mul(termTarget, termTarget, subresult);
      }
      hasFactors = true;
    } else if (strcmp(tok, ")") == 0) {
      break;
    } else if (strcmp(tok, "E") == 0) {
      break;
    } else if (strcmp(tok, "+") == 0 || strcmp(tok, "*") == 0) {
      //handled below
    } else if (strcmp(tok, "-") == 0) {
      negate = !negate;
      //remaining handled below
    } else {
      //Factor. (either constant or variable)
      mpq_t& factor = voc(tok, temp_q);
      if (!hasFactors) {
        mpq_set(termTarget, factor);
      } else {
        mpq_mul(termTarget, termTarget, factor);
      }
      hasFactors = true;
    }
  }

  //Emit last term, if necessary:
  if (hasFactors) {
    if (negate) {
      mpq_neg(termTarget, termTarget);
    }
    if (!hasTerms) {
      mpq_set(polyTarget, termTarget);
    } else {
      mpq_add(polyTarget, polyTarget, termTarget);
    }
    hasTerms = true;
    isEmpty = false;
    hasFactors = false;
    negate = false;
  }

  //Set to zero if the polynomial is empty
  if (isEmpty) {
    mpq_set_ui(polyTarget, 0, 1);
  }
}


// Expected format SI INPUT into LENGTH bits at FIRST_OUTPUT
void ComputationProver::compute_split_unsignedint(FILE* pws_file) {
  mpq_t* in = NULL;
  char cmds[BUFLEN];

  //cout << *cmds << endl;
  next_token_or_error(pws_file, cmds);

  if (cmds[0] == 'V') {
    in = &F1_q[F1_index[atoi(cmds + 1)]];
  } else if (cmds[0] == 'I') {
    in = &input_q[atoi(cmds + 1)];
  }
  expect_next_token(pws_file, "into", "Invalid SI");
  next_token_or_error(pws_file, cmds);
  int length = atoi(cmds);
  expect_next_token(pws_file, "bits", "Invalid SI");
  expect_next_token(pws_file, "at", "Invalid SI");
  ////cout << *cmds << endl;
  next_token_or_error(pws_file, cmds);
  int output_start = atoi(cmds + 1);

  //Fill in the Ni with the bits of in.
  //Each bit is either 0 or 1
  //gmp_printf("%Zd\n", in);
  for(int i = 0; i < length; i++) {
    mpq_t& Ni = F1_q[F1_index[output_start + i]];
    int bit = mpz_tstbit(mpq_numref(*in), length - i - 1);
    //cout << bit << endl;
    mpq_set_ui(Ni, bit, 1);
    //gmp_printf("%Zd\n", Ni);
  }
}

// Expected format SIL (uint | int) bits <length> X <input> Y0 <first bit of output>
void ComputationProver::compute_split_int_le(FILE* pws_file) {
  char cmds[BUFLEN];

  next_token_or_error(pws_file, cmds);
  bool isSigned = cmds[0] != 'u';
  expect_next_token(pws_file, "bits", "Invalid SIL");
  next_token_or_error(pws_file, cmds);
  int N = atoi(cmds);
  expect_next_token(pws_file, "X", "Invalid SIL");
  next_token_or_error(pws_file, cmds);
  mpq_t& in = voc(cmds, temp_q);
  expect_next_token(pws_file, "Y0", "Invalid SIL");
  next_token_or_error(pws_file, cmds);
  if (cmds[0] != 'V'){
    gmp_printf("Assertion Error: Cannot output split gate bits to %s, a V# was required.\n", cmds);
  }
  int output_start = atoi(cmds + 1);

  //Fill in the Ni with the bits of in 
  //Each bit is either 0 or 1
  //gmp_printf("%Zd\n", in);

  mpz_set(temp, mpq_numref(in));
  bool inIsNegative = mpz_sgn(temp) < 0;
  if (!isSigned && inIsNegative){
    gmp_printf("Assertion Error: Negative integer input to unsigned split gate\n");
  }
  if (inIsNegative){
    mpz_set_ui(temp2, 1);
    mpz_mul_2exp(temp2, temp2, N);
    mpz_add(temp, temp, temp2);
  }
  for(int i = 0; i < N; i++) {
    mpq_t& Ni = F1_q[F1_index[output_start + i]];
    if (i == N-1 && isSigned){
      mpz_set_ui(temp2, inIsNegative ? 1 : 0);
      //If the number is negative, then temp2 should be the sign bit.
      //Subtract it off.
      mpz_sub(temp, temp, temp2);
    } else {
      mpz_tdiv_r_2exp(temp2, temp, 1);
      mpz_tdiv_q_2exp(temp, temp, 1);
    }
    mpq_set_z(Ni, temp2);
  }
  if (mpz_sgn(temp)!=0){
    gmp_printf("Assertion Error: Some bits left over %Qd, in splitting %Qd to signed? %d bits %d\n", temp, in, isSigned, N);
  }
}

void ComputationProver::compute_less_than_int(FILE* pws_file) {
  char cmds[BUFLEN];

  expect_next_token(pws_file, "N_0", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  int N_start = atoi(cmds + 1);
  expect_next_token(pws_file, "N", "Invalid <I");
  int N = atoi(cmds);
  next_token_or_error(pws_file, cmds);
  expect_next_token(pws_file, "Mlt", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& Mlt = voc(cmds, temp_q);
  expect_next_token(pws_file, "Meq", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& Meq = voc(cmds, temp_q);
  expect_next_token(pws_file, "Mgt", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& Mgt = voc(cmds, temp_q);

  expect_next_token(pws_file, "X1", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& X1 = voc(cmds, temp_q);
  expect_next_token(pws_file, "X2", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& X2 = voc(cmds, temp_q);
  expect_next_token(pws_file, "Y", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& Y = voc(cmds, temp_q);

  int compare = mpq_cmp(X1, X2);
  if (compare < 0) {
    mpq_set_ui(Mlt, 1, 1);
    mpq_set_ui(Meq, 0, 1);
    mpq_set_ui(Mgt, 0, 1);
    mpq_sub(temp_qs[0], X1, X2);
  } else if (compare == 0) {
    mpq_set_ui(Mlt, 0, 1);
    mpq_set_ui(Meq, 1, 1);
    mpq_set_ui(Mgt, 0, 1);
    mpq_sub(temp_qs[0], X1, X2);
  } else if (compare > 0) {
    mpq_set_ui(Mlt, 0, 1);
    mpq_set_ui(Meq, 0, 1);
    mpq_set_ui(Mgt, 1, 1);
    mpq_sub(temp_qs[0], X2, X1);
  }
  mpq_set(Y, Mlt);

  mpz_set_ui(temp, 1);
  mpz_mul_2exp(temp, temp, N-1);
  mpz_add(temp, temp, mpq_numref(temp_qs[0]));

  //Fill in the Ni with the bits of the difference + 2^(N-1)
  //Each bit is either 0 or the power of two, so the difference = sum (Ni)
  for(int i = 0; i < N-1; i++) {
    mpq_t& Ni = F1_q[F1_index[N_start + i]];
    mpz_tdiv_r_2exp(temp2, temp, 1);
    mpq_set_z(Ni, temp2);
    mpq_mul_2exp(Ni, Ni, i);
    mpz_tdiv_q_2exp(temp, temp, 1);
  }
}

void ComputationProver::compute_less_than_float(FILE* pws_file) {
  char cmds[BUFLEN];
  expect_next_token(pws_file, "N_0", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  int N_start = atoi(cmds + 1);

  expect_next_token(pws_file, "Na", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  int Na = atoi(cmds);

  expect_next_token(pws_file, "N", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& N = voc(cmds, temp_q);

  expect_next_token(pws_file, "D_0", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  int D_start = atoi(cmds + 1);

  expect_next_token(pws_file, "Nb", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  int Nb = atoi(cmds);

  expect_next_token(pws_file, "D", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& D = voc(cmds, temp_q);

  expect_next_token(pws_file, "D", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& ND = voc(cmds, temp_q);

  expect_next_token(pws_file, "Mlt", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& Mlt = voc(cmds, temp_q);
  expect_next_token(pws_file, "Meq", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& Meq = voc(cmds, temp_q);
  expect_next_token(pws_file, "Mgt", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& Mgt = voc(cmds, temp_q);

  expect_next_token(pws_file, "X1", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& X1 = voc(cmds, temp_q);
  expect_next_token(pws_file, "X2", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& X2 = voc(cmds, temp_q);
  expect_next_token(pws_file, "Y", "Invalid <I");
  next_token_or_error(pws_file, cmds);
  mpq_t& Y = voc(cmds, temp_q);

  int compare = mpq_cmp(X1, X2);
  if (compare < 0) {
    mpq_set_ui(Mlt, 1, 1);
    mpq_set_ui(Meq, 0, 1);
    mpq_set_ui(Mgt, 0, 1);
    mpq_sub(temp_q, X1, X2);
    mpq_set_z(N, mpq_numref(temp_q));
    mpq_set_z(D, mpq_denref(temp_q)); //should be positive
  } else if (compare == 0) {
    mpq_set_ui(Mlt, 0, 1);
    mpq_set_ui(Meq, 1, 1);
    mpq_set_ui(Mgt, 0, 1);
    mpq_set_si(N, -1, 1);
    mpq_set_ui(D, 1, 1);
  } else if (compare > 0) {
    mpq_set_ui(Mlt, 0, 1);
    mpq_set_ui(Meq, 0, 1);
    mpq_set_ui(Mgt, 1, 1);
    mpq_sub(temp_q, X2, X1);
    mpq_set_z(N, mpq_numref(temp_q));
    mpq_set_z(D, mpq_denref(temp_q)); //should be positive
  }
  mpq_set(Y, Mlt);

  mpz_set_ui(temp, 1);
  mpz_mul_2exp(temp, temp, Na);
  mpz_add(temp, temp, mpq_numref(N)); //temp = 2^Na + (numerator of difference)

  //Fill in the Ni with the bits of the numerator difference + 2^Na
  //Each bit is either 0 or the power of two, so N = sum (Ni)
  for(int i = 0; i < Na; i++) {
    mpq_t& Ni = F1_q[F1_index[N_start + i]];
    mpz_tdiv_r_2exp(temp2, temp, 1);
    mpq_set_z(Ni, temp2);
    mpq_mul_2exp(Ni, Ni, i);
    mpz_tdiv_q_2exp(temp, temp, 1);
  }

  mpz_set(temp, mpq_numref(D));

  //Fill in the Di with whether the denominator is a particular power of
  //two.
  for(int i = 0; i < Nb + 1; i++) {
    mpq_t& Di = F1_q[F1_index[D_start + i]];
    mpz_tdiv_r_2exp(temp2, temp, 1);
    mpq_set_z(Di, temp2);
    mpz_tdiv_q_2exp(temp, temp, 1);
  }

  //Invert D.
  mpq_inv(D, D);
  //Compute N D
  mpq_mul(ND, N, D);
}

void ComputationProver::compute_db_get_bits(FILE* pws_file) {
  char cmds[BUFLEN];
  next_token_or_error(pws_file, cmds);
  mpq_t& index = voc(cmds, temp_q);
  uint32_t idx = mpz_get_ui(mpq_numref(index));
  next_token_or_error(pws_file, cmds);
  mpq_t& nb = voc(cmds, temp_q);
  uint32_t numBits = mpz_get_ui(mpq_numref(nb));

  Bits data = _ram->get(idx);
    if (numBits != data.size()) {
      gmp_printf("ERROR: compute_db_get_bits: wrong number of bits requested: index=%d, requested=%d, stored=%d\n",
          idx, numBits, data.size());
      exit(1);
    }

  //cout << "prover: get bits at " << idx << endl;
  for (uint32_t i = 0; i < numBits; i++) {
    //cout << data[i];
    next_token_or_error(pws_file, cmds);
    mpq_t& val = voc(cmds, temp_q);
    mpz_set_ui(mpq_numref(val), static_cast<uint32_t>(data[i]));
    mpq_canonicalize(val);
  }
  //cout << endl;
}

void ComputationProver::compute_db_put_bits(FILE* pws_file) {
  char cmds[BUFLEN];
  next_token_or_error(pws_file, cmds);
  mpq_t& index = voc(cmds, temp_q);
  uint32_t idx = mpz_get_ui(mpq_numref(index));
  next_token_or_error(pws_file, cmds);
  mpq_t& nb = voc(cmds, temp_q);
  uint32_t numBits = mpz_get_ui(mpq_numref(nb));

  Bits data(numBits);

  for (uint32_t i = 0; i < numBits; i++) {
    next_token_or_error(pws_file, cmds);
    mpq_t& val = voc(cmds, temp_q);
    uint32_t bit = mpz_get_ui(mpq_numref(val));

    if (bit != 0 && bit != 1) {
      gmp_printf("ERROR: compute_db_put_bits: input is not a bit: index=%d, input=%d, bit_index=%d\n",
          idx, bit, i);
      exit(1);
    }

    data[i] = static_cast<bool>(bit);
  }

  _ram->put(idx, data);
}

void ComputationProver::compute_db_get_sibling_hash(FILE* pws_file) {
  char cmds[BUFLEN];
  next_token_or_error(pws_file, cmds);
  mpq_t& index = voc(cmds, temp_q);
  uint32_t idx = mpz_get_ui(mpq_numref(index));
  next_token_or_error(pws_file, cmds);
  mpq_t& level = voc(cmds, temp_q);
  uint32_t lvl = mpz_get_ui(mpq_numref(level));
  next_token_or_error(pws_file, cmds);
  int hashVarStart = atoi(cmds + 1);

  Bits hash;
  bool found = _ram->getSiblingHash(idx, lvl, hash);
  if (!found) {
    gmp_printf("ERROR: Sibling hash not found: index=%d, level=%d\n", idx, lvl);
    exit(1);
  }

  int numBits = _ram->getNumHashBits();
  for (int i = 0; i < numBits; i++) {
    mpq_t& hashVar = F1_q[F1_index[hashVarStart + i]];
    // Output bits in big endian for compatibility with other functions (e.g. SI)
    mpz_set_ui(mpq_numref(hashVar), static_cast<uint32_t>(hash[numBits - i - 1]));
    mpq_canonicalize(hashVar);
  }
}

void ComputationProver::parse_hash(FILE* pws_file, HashBlockStore::Key& outKey, int numHashBits) {
  char cmds[BUFLEN];

  outKey.resize(numHashBits);
  for (int i = 0; i < numHashBits; i++) {
    next_token_or_error(pws_file, cmds);
    if (strcmp(cmds, "NUM_X") == 0 || strcmp(cmds, "NUM_Y") == 0) {
      gmp_printf("ERROR: parse_hash: wrong number of hash vars: expected=%d, actual=%d\n", numHashBits, i);
      exit(1);
    }

    mpq_t& val = voc(cmds, temp_q);
    uint32_t bit = mpz_get_ui(mpq_numref(val));
    outKey[i] = static_cast<bool>(bit);
  }
}

void ComputationProver::compute_get_block_by_hash(FILE* pws_file) {
  char cmds[BUFLEN];

  HashBlockStore::Key key;
  parse_hash(pws_file, key, _ram->getNumHashBits());

  HashBlockStore::Value block;
  uint32_t blockSize = 0;

  // Special case: if the key == 0, don't fail. Just return zeroes.
  if (key.any()) {
    bool found = _blockStore->get(key, block);
    if (!found) {
      int numHashBits = _ram->getNumHashBits();

      std::string s;
      boost::to_string(key, s);
      gmp_printf("ERROR: compute_get_block_by_hash: block not found: hash=\n");
      for (int i = 0; i < numHashBits; i++) {
        cout<<key[numHashBits-i];
      }
      cout<<endl;
      exit(1);
    }

    blockSize = block.size();
  }

  expect_next_token(pws_file, "NUM_Y", "compute_get_block_by_hash: expected NUM_Y");

  next_token_or_error(pws_file, cmds);
  mpq_t& nb = voc(cmds, temp_q);
  uint32_t numBits = mpz_get_ui(mpq_numref(nb));

  expect_next_token(pws_file, "Y", "compute_get_block_by_hash: expected Y");

  for (uint32_t i = 0; i < numBits; i++) {
    next_token_or_error(pws_file, cmds);
    mpq_t& val = voc(cmds, temp_q);

    // Pad with zeroes
    uint32_t bit = 0;
    if (i < blockSize) {
      bit = static_cast<int>(block[i]);
    }
    mpz_set_ui(mpq_numref(val), bit);
    mpq_canonicalize(val);
  }
}

void ComputationProver::compute_put_block_by_hash(FILE* pws_file) {
  char cmds[BUFLEN];

  HashBlockStore::Key key;
  parse_hash(pws_file, key, _ram->getNumHashBits());
  HashBlockStore::Value block;

  expect_next_token(pws_file, "NUM_X", "compute_put_block_by_hash: expected NUM_X");

  next_token_or_error(pws_file, cmds);
  mpq_t& nb = voc(cmds, temp_q);
  uint32_t numBits = mpz_get_ui(mpq_numref(nb));

  expect_next_token(pws_file, "X", "compute_put_block_by_hash: expected X");

  block.resize(numBits);

  //	gmp_printf("compute_put_block_by_hash: value=");
  for (uint32_t i = 0; i < numBits; i++) {
    next_token_or_error(pws_file, cmds);
    mpq_t& val = voc(cmds, temp_q);
    uint32_t bit = mpz_get_ui(mpq_numref(val));

    if (bit != 0 && bit != 1) {
      gmp_printf("ERROR: compute_put_block_by_hash: input is not a bit: input=%d, bit_index=%d\n", bit, i);
      exit(1);
    }

    //		gmp_printf("%d", bit);

    block[i] = static_cast<bool>(bit);
  }
  //	gmp_printf("\n");

  // Special case: if the key == 0, dont't store the block.
  if (key.any()) {
    _blockStore->put(key, block);
  }
}

void ComputationProver::compute_free_block_by_hash(FILE* pws_file) {
  HashBlockStore::Key key;
  parse_hash(pws_file, key, _ram->getNumHashBits());
  _blockStore->free(key);
}

void ComputationProver::compute_printf(FILE* pws_file) {
  char cmds[BUFLEN];

  std::string format;
  while(true){
    next_token_or_error(pws_file, cmds);
    if (strcmp(cmds, "NUM_X")) {
      break;
    }
    format += cmds;
    format += " ";
  }
  next_token_or_error(pws_file, cmds);
  int num_args = atoi(cmds);

  expect_next_token(pws_file, "X", "Format error in printf");

  int64_t args [10];
  if (num_args > 10){
    cout << "ERROR: Cannot have more than 10 arguments to prover's printf!" << endl;
    num_args = 10;
  }

  for(int i = 0; i < num_args; i++){
    next_token_or_error(pws_file, cmds);
    mpq_t& arg = voc(cmds, temp_q);
    args[i] = mpz_get_si(mpq_numref(arg));
  }

  gmp_printf("PRINTF in computation_p %d:\n", num_args);
  gmp_printf(format.c_str(), args[0], args[1], args[2], args[3],
  args[4], args[5], args[6], args[7], args[8], args[9]);
}

void ComputationProver::compute_genericget(FILE* pws_file) {
  char cmds[BUFLEN];

  expect_next_token(pws_file, "COMMITMENT", "For now, only COMMITMENT is allowed in genericGET");

  expect_next_token(pws_file, "NUM_HASH_BITS", "Format error in genericget 1");

  next_token_or_error(pws_file, cmds);

  expect_next_token(pws_file, "HASH_IN", "Format error in genericget 2");

  HashBlockStore::Key key;
  parse_hash(pws_file, key, NUM_COMMITMENT_BITS);

  HashBlockStore::Value block;
  uint32_t blockSize = 0;

  // Special case: if the key == 0, don't fail. Just return zeroes.
  if (key.any()) {
    bool found = _blockStore->get(key, block);
    if (!found) {
      int numHashBits = NUM_COMMITMENT_BITS;

      std::string s;
      boost::to_string(key, s);
      gmp_printf("ERROR: compute_genericget: block not found: hash=\n");
      for (int i = 0; i < numHashBits; i++) {
        cout<<key[i];
      }
      cout<<endl;
      exit(1);
    }

    blockSize = block.size();
  }

  expect_next_token(pws_file, "NUM_Y", "compute_genericget: expected NUM_Y");

  next_token_or_error(pws_file, cmds);
  mpq_t& nb = voc(cmds, temp_q);
  uint32_t numBits = mpz_get_ui(mpq_numref(nb));

  expect_next_token(pws_file, "Y", "compute_genericget: expected Y");

  for (uint32_t i = 0; i < numBits; i++) {
    next_token_or_error(pws_file, cmds);
    mpq_t& val = voc(cmds, temp_q);

    // Pad with zeroes
    uint32_t bit = 0;
    if (i < blockSize) {
      bit = static_cast<int>(block[i]);
    }
    mpz_set_ui(mpq_numref(val), bit);
    mpq_canonicalize(val);
  }
}

/**
 * If str is the name of a variable, return a reference to that variable.
 * Otherwise, set use_if_constant to the constant variable held by the
 * string, and return it.
 *
 * The method name stands for "variable or constant"
 **/
//mpq_t& ComputationProver::voc(const std::string& str, mpq_t& use_if_constant) {
mpq_t& ComputationProver::voc(const char* str, mpq_t& use_if_constant) {
  int index;
  const char* name = str;
  if (name[0] == 'V') {
    index = atoi(name + 1);
    if (index < 0 || index >= num_vars) {
      gmp_printf("PARSE ERROR - variable %s\n",str);
      return use_if_constant;
    }
    return F1_q[F1_index[index]];
  } else if (name[0] == 'I') {
    index = atoi(name + 1);
    if (index < 0 || index >= size_input) {
      gmp_printf("PARSE ERROR - variable %s\n",str);
      return use_if_constant;
    }
    return input_output_q[index];
  } else if (name[0] == 'O') {
    index = atoi(name + 1);
    if (index < size_input || index >= size_input + size_output) {
      gmp_printf("PARSE ERROR - variable %s\n",str);
      return use_if_constant;
    }
    return input_output_q[index];
  }
  //Parse the rational constant
  mpq_set_str(use_if_constant, str, 10);
  return use_if_constant;
}

//void ComputationProver::compute_matrix_vec_mul(std::istream_iterator<std::string>& cmds) {
void ComputationProver::compute_matrix_vec_mul(FILE* pws_file) {
  char cmds[BUFLEN];

  expect_next_token(pws_file, "NUM_ROWS", "Invalid MATRIX_VEC_MUL, NUM_ROWS exected.");
  next_token_or_error(pws_file, cmds);
  int number_of_rows = atoi(cmds);

  expect_next_token(pws_file, "NUM_COLUMNS", "Invalid MATRIX_VEC_MUL, NUM_COLUMNS expected.");
  next_token_or_error(pws_file, cmds);
  int number_of_columns = atoi(cmds);

  expect_next_token(pws_file, "ACTUAL_NUM_COLUMNS", "Invalid MATRIX_VEC_MUL, ACTUAL_NUM_COLUMNS expected.");
  next_token_or_error(pws_file, cmds);
  int actual_number_of_columns = atoi(cmds);

  // read input bits from F1
  expect_next_token(pws_file, "IN_VEC", "Invalid MATRIX_VEC_MUL, IN_VEC expected.");

  mpq_t *input, *result;
  alloc_init_vec(&input, actual_number_of_columns);
  alloc_init_vec(&result, number_of_rows);

  for (int i = 0; i < actual_number_of_columns; i++) {
    next_token_or_error(pws_file, cmds);
    mpq_set(input[i], voc(cmds, temp_q));
  }

  // compute ggh hash and get output
  const uint32_t* row = AMat;
  mpq_t factor;
  mpq_t term;
  mpq_inits(factor, term, NULL);
  for (int i = 0; i < number_of_rows; i++, row += number_of_columns) {
    mpq_set_ui(result[i], 0, 1);
    for (int j = 0; j < actual_number_of_columns; j++) {
      mpq_set_ui(factor, row[j], 1);
      mpq_mul(term, factor, input[j]);
      mpq_add(result[i], result[i], term);
    }
  }
  mpq_clears(factor, term, NULL);

  // assign output to output variables
  expect_next_token(pws_file, "OUT_VEC", "Invalid MATRIX_VEC_MUL, IN_VEC expected.");

  for (int i = 0; i < number_of_rows; i++) {
    //mpq_t& output = voc(*cmds,temp_q); cmds++;
    next_token_or_error(pws_file, cmds);
    mpq_t& output = voc(cmds, temp_q);
    mpq_set(output, result[i]);
  }

  clear_del_vec(input, actual_number_of_columns);
  clear_del_vec(result, number_of_rows);
}

/**
  The computation may elect to simply execute a PWS file (prover work sheet).
  This routine parses a PWS file (filename in a C-string) and parses it.
  */
void ComputationProver::compute_from_pws(const char* pws_filename) {
  std::ifstream cmdfile (pws_filename);
  FILE* pws_file = fopen(pws_filename, "r");

  if (pws_file == NULL) {
    gmp_printf("Couldn't open prover worksheet file.\n");
    return;
  }

  // do not read the whole pws file into memory.
  char tok[BUFLEN], cmds[BUFLEN];
  while(try_next_token(pws_file, tok) != EOF) {
    if (strcmp(tok, "P") == 0) {
      next_token_or_error(pws_file, cmds);
      mpq_t& Y = voc(cmds, temp_q);
      expect_next_token(pws_file, "=", "Invalid POLY");
      compute_poly(pws_file, 0);
      mpq_set(Y, temp_qs[0]);
    } else if (strcmp(tok, "<I") == 0) {
      compute_less_than_int(pws_file);
    } else if (strcmp(tok, "<F") == 0) {
      compute_less_than_float(pws_file);
    } else if (strcmp(tok, "!=") == 0) {
      //Not equals computation
      expect_next_token(pws_file, "M", "Invalid !=");
      next_token_or_error(pws_file, cmds);
      mpq_t& M = voc(cmds, temp_q);
      expect_next_token(pws_file, "X1", "Invalid !=");
      next_token_or_error(pws_file, cmds);
      mpq_t& X1 = voc(cmds, temp_q);
      expect_next_token(pws_file, "X2", "Invalid !=");
      next_token_or_error(pws_file, cmds);
      mpq_t& X2 = voc(cmds, temp_q2);
      expect_next_token(pws_file, "Y", "Invalid !=");
      next_token_or_error(pws_file, cmds);
      mpq_t& Y = voc(cmds, temp_q);

      if (mpq_equal(X1, X2)) {
        mpq_set_ui(M, 0, 1);
        mpq_set_ui(Y, 0, 1);
      } else {
        mpq_sub(temp_q, X1, X2);
        //f(a,b)^-1 = b*a^-1
        mpz_invert(temp, mpq_numref(temp_q), prime);
        mpz_mul(temp, temp, mpq_denref(temp_q));
        mpq_set_z(M, temp);
        mpq_set_ui(Y, 1, 1);
      }
    } else if (strcmp(tok, "/") == 0 || strcmp(tok, "/I") == 0 || strcmp(tok, "%I") == 0) {
      //Binary operation 
      next_token_or_error(pws_file, cmds);
      mpq_t& Y = voc(cmds, temp_q);
      expect_next_token(pws_file, "=", ("Invalid "+std::string(tok)).c_str());
      next_token_or_error(pws_file, cmds);
      mpq_t& X1 = voc(cmds, temp_q);
      expect_next_token(pws_file, tok, ("Invalid "+std::string(tok)).c_str());
      next_token_or_error(pws_file, cmds);
      mpq_t& X2 = voc(cmds,temp_q2);
      if (strcmp(tok, "/") == 0) {
        //Exact division
        mpq_div(Y,X1,X2);
      } else if (strcmp(tok, "/I") == 0) {
        mpz_tdiv_q(mpq_numref(Y), mpq_numref(X1), mpq_numref(X2));
        mpz_set_ui(mpq_denref(Y),1);
      } else if (strcmp(tok, "%I") == 0) {
        mpz_tdiv_r(mpq_numref(Y), mpq_numref(X1), mpq_numref(X2));
        mpz_set_ui(mpq_denref(Y),1);
      }
    } else if (strcmp(tok, "SI") == 0) {
      //Split into bits (big endian, see implementation for format)
      compute_split_unsignedint(pws_file);
    } else if (strcmp(tok, "SIL") == 0) {
      compute_split_int_le(pws_file);
    } else if (strcmp(tok, "MATRIX_VEC_MUL") == 0) {
      compute_matrix_vec_mul(pws_file);
    } else if (strcmp(tok, "DB_GET_BITS") == 0) {
      compute_db_get_bits(pws_file);
    } else if (strcmp(tok, "DB_PUT_BITS") == 0) {
      compute_db_put_bits(pws_file);
    } else if (strcmp(tok, "DB_GET_SIBLING_HASH") == 0) {
      compute_db_get_sibling_hash(pws_file);
    } else if (strcmp(tok, "GET_BLOCK_BY_HASH") == 0) {
      compute_get_block_by_hash(pws_file);
    } else if (strcmp(tok, "PUT_BLOCK_BY_HASH") == 0) {
      compute_put_block_by_hash(pws_file);
    } else if (strcmp(tok, "FREE_BLOCK_BY_HASH") == 0) {
      compute_free_block_by_hash(pws_file);
    } else if (strcmp(tok, "GENERICGET") == 0) {
      compute_genericget(pws_file);
    } else if (strcmp(tok, "PRINTF") == 0) {
      compute_printf(pws_file);
    } else if (strcmp(tok, "ASSERT_ZERO") == 0) {
      next_token_or_error(pws_file, cmds);
      mpq_t& Y = voc(cmds, temp_q);
      //std::string var(*cmds);
      //cmds++;
      std::string var(cmds);
      if (mpq_sgn(Y) != 0){
        cout << "ASSERT_ZERO FAILED: " << var << endl;
        ////exit(1);
      }
    } else {
      gmp_printf("Unrecognized token: %s\n", tok);
    }
  }

  // convert output_q to output
  convert_to_z(size_output, output, output_q, prime);

  // convert F1_q to F1
  convert_to_z(num_vars, F1, F1_q, prime);
}
