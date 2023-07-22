#!/bin/sh

#PBS -l pmem=4gb
#PBS -l walltime=240:00

echo >> 'scoring.cert.out'
pwd >> 'scoring.cert.out'
echo -n 'HOST: ' >> 'scoring.cert.out'
hostname >> 'scoring.cert.out'
echo >> 'scoring.cert.out'
echo Environment variables: >> 'scoring.cert.out'
echo ACL2_CUSTOMIZATION=NONE >> 'scoring.cert.out'
echo ACL2_SYSTEM_BOOKS=/Users/kitku/dev/acl2/books >> 'scoring.cert.out'
echo ACL2=acl2s >> 'scoring.cert.out'
echo ACL2_USELESS_RUNES=-25 >> 'scoring.cert.out'
echo >> 'scoring.cert.out'
echo Temp lisp file: >> 'scoring.cert.out'
cat 'workxxx.scoring.cert.1061771851.LISP' >> 'scoring.cert.out'
echo --- End temp lisp file --- >> 'scoring.cert.out'
echo >> 'scoring.cert.out'
echo TARGET: scoring >> 'scoring.cert.out'
echo STEP: certify >> 'scoring.cert.out'
echo Start of output: >> 'scoring.cert.out'
echo >> 'scoring.cert.out'
export ACL2_WRITE_PORT=t
(acl2s < 'workxxx.scoring.cert.1061771851.LISP' 2>&1) >> 'scoring.cert.out'
EXITCODE=$?
echo Exit code from ACL2 is $EXITCODE >> 'scoring.cert.out'
ls -l 'scoring.cert' >> 'scoring.cert.out' || echo 'scoring.cert' seems to be missing >> 'scoring.cert.out'
exit $EXITCODE
