
ntusat is based on Simpsat in SAT Competition 2012 which is an enhanced version of CRYPTOMINISAT 2.9.2. Adding pure literal implication clauses from time to time could make the theory not functional equivalent but reduce the search space to help the solver solve faster.
Please see ntusatbreak.pdf for more technique details.


name:   ntusat
version: 1.1
author: Hsiao-Lun, Wang and Jie Hong, Roland Jiang

compile:

sh build.sh


execute:

./runBreakIDntusat.sh  <instance>   <tempdir>

