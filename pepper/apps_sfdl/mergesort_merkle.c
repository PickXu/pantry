#include <stdint.h>

#define MAX_SIZE 8

struct In { uint32_t input[MAX_SIZE]; } ;
struct Out { uint32_t output[MAX_SIZE]; } ;

void compute(struct In *input, struct Out *output) {
    int bPtr, ePtr, mPtr, lPtr, rPtr, span;
    int i;
    int inOffset = 0;
    int outOffset = MAX_SIZE;
    int tmpi;
    uint32_t tmp1, tmp2;

    // first, copy input into RAM
    for (i = 0; i < MAX_SIZE; i++) {
        ramput(i, &(input->input[i]));
    }

    // now sort
    for (span = 1; span < MAX_SIZE; span *= 2) {
        // MAX_SIZE had better be a power of 2!!!

        for (bPtr = 0; bPtr < MAX_SIZE; bPtr += 2*span) {
            lPtr = bPtr;
            mPtr = lPtr + span;
            rPtr = mPtr;
            ePtr = rPtr + span;

            // since loops get unrolled at compile time, these branches do not appear in the circuit
            for (i=lPtr; i<ePtr; i++) {
                ramget(&tmp1, lPtr + inOffset);
                ramget(&tmp2, rPtr + inOffset);
                if ( (lPtr < mPtr) && ( (! (rPtr < ePtr)) || (tmp1 < tmp2) ) ) {
                    tmp2 = tmp1;
                    lPtr++;
                } else {
                    rPtr++;
                }
                ramput(i+outOffset, &tmp2);
            }
        }

        tmpi = inOffset;
        inOffset = outOffset;
        outOffset = tmpi;
    }

    // now copy output from RAM
    // note that we've swapped in and out offsets, so our output now sits at inOffset
    for (i = 0; i < MAX_SIZE; i++) {
        ramget(&(output->output[i]), i + inOffset);
    }
}

