#!/bin/bash
cd "$(dirname "$0")"
NPAR=$1; shift
for f in "$@"; do
  while [ "$(jobs -rp | wc -l)" -ge "$NPAR" ]; do sleep 2; done
  python dns2d.py runs/$f.json runs/$f.out.json > runs/$f.log 2>&1 &
done
wait
