#! /bin/bash

echo "------------------------------------------"
echo "Statements to prove in files: "
find theories -name "*.v" -exec grep -le [Aa]dmit {} \;
echo "------------------------------------------"
echo -n "To prove: "
echo $(find theories -name "*.v" -exec grep -He [Aa]dmit {} \; | wc -l)
echo "------------------------------------------"