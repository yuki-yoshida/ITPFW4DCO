#! /bin/bash
~/cafeobj-1.5.6-sbcl-x64Darwin-2/bin/cafeobj -batch all.cafe | grep '^root\*' | wc
echo should be 15 lines
