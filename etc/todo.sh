#! /bin/bash

echo "------------------------------------------"
echo "Statements to prove in files: "
find . -name "*.v" -exec grep -le [Aa]dmit {} \;
echo "------------------------------------------"
echo -n "To prove: "
echo $(find . -name "*.v" -exec grep -He [Aa]dmit {} \; | wc -l)
echo "------------------------------------------"