
#define NUM_OF_BITS 5376
#define BITS_IN_UINT32 32

#define BLOCKLEN (NUM_OF_BITS/BITS_IN_UINT32)

#define NUM_OF_BLOCKS 20

struct Block {
  uint32_t block[BLOCKLEN];
};

struct In {
  struct Block blocks[NUM_OF_BLOCKS];
};

struct Out {
  hash_t hashes[NUM_OF_BLOCKS];
};

