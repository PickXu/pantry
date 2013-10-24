#ifndef _MR_BSTORE_DOTP_H
#define _MR_BSTORE_DOTP_H

#include <stdint.h>

#define NUM_MAPPERS 10
#define NUM_REDUCERS 1

#define SIZE_INPUT 20000

// actual input to the mapper
typedef struct _MapperIn {
  uint32_t vec_a[SIZE_INPUT];
  uint32_t vec_b[SIZE_INPUT];
} MapperIn;

// actual output of the mapper
typedef struct _MapperChunkOut {
  uint32_t output;
} MapperChunkOut;

typedef struct _MapperOut {
  MapperChunkOut output[NUM_REDUCERS];
} MapperOut;

typedef struct _ReducerChunkIn {
  uint32_t input;
} ReducerChunkIn;

typedef struct _ReducerIn {
  ReducerChunkIn input[NUM_MAPPERS];
} ReducerIn;

typedef struct _ReducerOut {
  uint32_t output;
} ReducerOut;

#endif
