#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>

#ifndef MAX_SIZE
#define MAX_SIZE 8
#endif 

#define BUFFER_SIZE 1024
#define BUFFER_CHUNK 10*BUFFER_SIZE

#define _ELM_TYPE int

struct In {_ELM_TYPE input[MAX_SIZE];};
struct Out {_ELM_TYPE output[MAX_SIZE];};

void compute(struct In *input, struct Out *output);

int main(int argc, char **argv) {
    int i;
    struct In foo = {{0,}};
    struct Out bar = {{0,}};

    int nRead = 0;
    char buf[BUFFER_SIZE];
    int inStrSize = BUFFER_CHUNK;
    char *inString = malloc(inStrSize*sizeof(char));
    char *tok, *stok;
    char *saveptr1, *saveptr2, *str1, *str2;

    if ((argc == 0) || (argv == 0)) { exit(-1); }

    while (0 < (nRead = read(STDIN_FILENO,buf,1024))) {
        if (i + nRead > inStrSize) { // assumes that BUFFER_CHUNK 
            inStrSize += BUFFER_CHUNK;
            if (NULL == (inString = realloc(inString,inStrSize))) {
                perror("failed to realloc inString");
                exit(-1);
            }
        }
        memcpy(inString + i, buf, nRead);
        i += nRead;
    }
    inString[i] = '\0';  // null terminate

    // tokenize on spaces, braces
    // skip first token (this is length, but we've hard coded it for now)
    for (i=-1, str1 = inString ; ; i++, str1 = NULL) {
        tok = strtok_r(str1," []",&saveptr1);

        if (i < 0) { continue; }
        else if (i == MAX_SIZE || NULL == tok) { break; }

        // tokenize on rational notation, e.g., 5%2
        // note that we turn these into integers!
        for (str2 = tok; ; str2 = NULL) {
            stok = strtok_r(str2," %",&saveptr2);

            if (NULL == stok) { break; }

            if (str2 != NULL) {
                foo.input[i] = (_ELM_TYPE) atoi(stok);
            } else {
                foo.input[i] /= (_ELM_TYPE) atoi(stok);
            }
        }
    }

    compute(&foo,&bar);

    for (i=0; i<MAX_SIZE; i++) {
        printf("%u ",bar.output[i]);
        fprintf(stderr,"%u ",bar.output[i]);
    }

    return 0;
}

void compute(struct In *input, struct Out *output) {
    int bPtr, ePtr, mPtr, lPtr, rPtr;
    int span;
    int i;
    bool out2in = false;
    _ELM_TYPE *dst, *src;

    for (span = 1; span < MAX_SIZE; span *= 2) {
        // MAX_SIZE had better be a power of 2!!!

        // out2in means we're going out->in and need to copy back at the end
        if (out2in) {
            src = output->output;
            dst = input->input;
        } else {    // otherwise we're going input->output
            src = input->input;
            dst = output->output;
        }

        for (bPtr = 0; bPtr < MAX_SIZE; bPtr += 2*span) {
            lPtr = bPtr;
            mPtr = lPtr + span;
            rPtr = mPtr;
            ePtr = rPtr + span;

            for (i=lPtr; i<ePtr; i++) {
                if ( (lPtr < mPtr) && ( (rPtr >= ePtr) || (src[lPtr] < src[rPtr]) ) ) {
                    dst[i] = src[lPtr++];
                } else {
                    dst[i] = src[rPtr++];
                }
            }
        }

        out2in = ! out2in;
    }

    if (!out2in) {  // note, !out2in here because it was negated just above
        for (i=0; i<MAX_SIZE; i++) {
            output->output[i] = input->input[i];
        }
    }
}
