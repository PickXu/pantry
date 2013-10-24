s source code is released under a BSD-style license. See LICENSE
for more details.


I. Installation
  
  Our code can either use Open MPI or HTTP for communication between the
  client and server; in our experiments, we used Open MPI. The following
  are the dependent packages, if installing in the Open MPI mode:

  1. gmp with C++ extensions enabled
  2. PAPI
  3. Chacha pseudorandom number generator (use the assembly version for
  high performance)
  4. NTL with NTL_GMP_LIP=on 
  5. libconfig
  6. Cheetah template library
  7. OpenMPI
  8. CUDA packages (if USE_GPU is set to 1 in GNUMakefile)
  9. GMPMEE 
 10. go
 11. python
 12. OpenSSL
 13. fcgi
 14. PBC (from Stanford)
 15. ant
 16. boost
 17. LevelDB
 18. KyotoCabinet
 19. libzm (from https://github.com/herumi/ate-pairing.git)

II. Configuration

  - By default, our build system selects the Zaatar protocol; however,
    to manually select another protocol, modify the variable FRAMEWORK
    in pepper/flags (e.g., "FRAMEWORK=GINGER").

III. Running examples
  
  (1) With a single machine, for testing purposes.

  Suppose the computation is apps_sfdl/mm.c, then do the following.

    Specify input sizes in apps_sfdl/mm.c

    Run "make C_FILES=mm_c"
    
    #Note - The first time a new computation is being compiled, the above command will
    #fail with "No target to compile ... _p_exo.o". In this case, re-run
    #the above command and it should work.
    
    To test, use pepper/run/run_pepper.sh

  (2) With a cluster, for experiments.

    Please refer to
    http://www.tacc.utexas.edu/user-services/user-guides/longhorn-user-guide
    for launching a job on TACC. 

IV. Contact
Please contact srinath at cs dot utexas dot edu for any questions and
comments.
