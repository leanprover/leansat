#!/bin/bash

export LC_ALL=C

LIB="Eval"
RUN_SUCCESSES="$LIB/run_success.txt"
RUN_FAILS="$LIB/run_fail.txt"

# Reset temporary files
> $RUN_SUCCESSES
> $RUN_FAILS

ulimit -s unlimited

# Build every file and memorize the results in run_[success|fail].txt
for path in $(find "${LIB}" -type f  -name "*.lean" | sort); do
    file_name_wo_suffix=$(basename -s .lean $path)
    echo "Trying $LIB.${file_name_wo_suffix}"
    lake build $LIB.${file_name_wo_suffix} > /dev/null 2>&1
    if [ $? -eq 0 ]; then
        echo $(basename $path) >> $RUN_SUCCESSES
    else
        echo $(basename $path) >> $RUN_FAILS
    fi
done

diff -u "${LIB}/fail.txt" $RUN_FAILS
exit $?
