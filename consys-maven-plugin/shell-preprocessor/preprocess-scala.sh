#!/bin/sh
###
# Usage: preprocess-scala.sh <dir>
# Preprocesses all scala files in the given directory.
# Creates backup files.
###
# See also: https://unix.stackexchange.com/questions/112023/how-can-i-replace-a-string-in-a-files
###
find $1 -iname '*.scala' -type f -exec sed -E -i.bak -f patterns-scala.txt {} \;
