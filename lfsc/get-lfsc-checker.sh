#!/usr/bin/env bash

# A script to download and build the LFSC checker. Based on
# https://github.com/cvc5/cvc5/blob/main/contrib/get-lfsc-checker

# utility function to download a file
function download {
  if [ -x "$(command -v wget)" ]; then
    wget -c -O "$2" "$1"
  elif [ -x "$(command -v curl)" ]; then
    curl -L "$1" >"$2"
  else
    echo "Can't figure out how to download from web. Please install wget or curl." >&2
    exit 1
  fi
}

KIND_DIR=$(dirname $(dirname "$0"))
pushd $KIND_DIR/lfsc

BASE_DIR=`pwd`
mkdir -p $BASE_DIR/tmp/

# download and unpack LFSC
version="5f44ffb1241ca81dbb3118807546ba14ab9ea7a5"
download "https://github.com/cvc5/LFSC/archive/$version.tar.gz" $BASE_DIR/tmp/lfsc.tgz
tar --strip 1 -xzf $BASE_DIR/tmp/lfsc.tgz -C $BASE_DIR
rm -r $BASE_DIR/tmp

# build and install LFSC
mkdir -p build && cd build
cmake -DCMAKE_INSTALL_PREFIX="$BASE_DIR" ..
make install

##### signatures

# The LFSC signatures live in the main cvc5 repository
version="673bdf617a72e75f474fa33b82301fa1d987a829"
SIG_DIR_URL="https://raw.githubusercontent.com/cvc5/cvc5/$version/proofs/lfsc/signatures"

# install signatures and scripts
pushd $BASE_DIR/signatures
download $SIG_DIR_URL/core_defs.plf core_defs.plf
download $SIG_DIR_URL/util_defs.plf util_defs.plf
download $SIG_DIR_URL/theory_def.plf theory_def.plf
download $SIG_DIR_URL/nary_programs.plf nary_programs.plf
download $SIG_DIR_URL/boolean_programs.plf boolean_programs.plf
download $SIG_DIR_URL/boolean_rules.plf boolean_rules.plf
download $SIG_DIR_URL/cnf_rules.plf cnf_rules.plf
download $SIG_DIR_URL/equality_rules.plf equality_rules.plf
download $SIG_DIR_URL/arith_programs.plf arith_programs.plf
download $SIG_DIR_URL/arith_rules.plf arith_rules.plf
download $SIG_DIR_URL/quantifiers_rules.plf quantifiers_rules.plf
popd

# Script for checking LFSC proofs generated by Kind 2
cat << EOF > $BASE_DIR/bin/lfsc-check.sh
#!/bin/bash

cat \$@ | grep WARNING
CHECK=\$(cat \$@ | grep check)
[ -z "\$CHECK" ] && echo "; WARNING: Empty proof!!!"

SIG_DIR=$BASE_DIR/signatures
SIGS="\$SIG_DIR/core_defs.plf \\
    \$SIG_DIR/util_defs.plf \\
    \$SIG_DIR/theory_def.plf \\
    \$SIG_DIR/nary_programs.plf \\
    \$SIG_DIR/boolean_programs.plf \\
    \$SIG_DIR/boolean_rules.plf \\
    \$SIG_DIR/cnf_rules.plf \\
    \$SIG_DIR/equality_rules.plf \\
    \$SIG_DIR/arith_programs.plf \\
    \$SIG_DIR/arith_rules.plf \\
    \$SIG_DIR/quantifiers_rules.plf \\
    \$SIG_DIR/kind.plf"
### Release version
$BASE_DIR/bin/lfscc \$SIGS \$@

### Debugging version
#$BASE_DIR/bin/lfscc \$SIGS \$@ >& lfsc.out

## recover macros for applications of arity 1,2,3, and simplify builtin syntax for constants
##sed -i.orig 's/(f_ite [^ \)]*)/f_ite/g' lfsc.out
#sed -i.orig 's/(\\ [^ ]* (\\ [^ ]* (\\ [^ ]* (apply (apply (apply f_\([^ ]*\) [^ ]*) [^ ]*) [^ ]*))))/\1/g; s/(\\ [^ ]* (\\ [^ ]* (apply (apply f_\([^ ]*\) [^ ]*) [^ ]*)))/\1/g; s/(\\ [^ ]* (apply f_\([^ ]*\) [^ ]*))/\1/g; s/(var \([^ ]*\) [^ \)]*)/var_\1/g; s/(int \([^ \)]*\))/\1/g; s/emptystr/""/g; s/int\.//g' lfsc.out
#
#cat lfsc.out
#rm lfsc.out
EOF
chmod +x $BASE_DIR/bin/lfsc-check.sh

popd

echo ""
echo "========== How to use LFSC =========="
echo "Check a generated proof:"
echo "  $BASE_DIR/bin/lfsc-check.sh <proof file>"
