#!/bin/bash
file="$1"
verify="`find . -name Verify.byte -print -quit`"
if [[ $verify ]] 
then 
    echo -n ''
else
    verify="`which Verify.byte`"
fi

name="`egrep '^Name:' $file | sed s/'^Name:'//g`"
input="`egrep '^Input:' $file | sed s/'^Input:'//g`"
program="`egrep -v -e '^Input:' -v -e '^Name:' -v -e '^Output:' -v -e '^Result:' $file | sed s/'^Program:'//`"
output="`egrep '^Output:' $file | sed s/'^Output:'//g`"
result="`egrep '^Result:' $file | sed s/'^Result:'//g`"

echo -n "starting verify. input: "
echo -n "$input"
echo -n ", output: "
echo -n "$output"
echo -n ", program: "
echo "$program"
$verify -f NetKAT -m reach "$name" "$input" "$program" "$output"

