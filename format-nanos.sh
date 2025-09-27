#!/bin/bash
let "ns_per_sec = 1000 * 1000 * 1000"
let "ns_per_min = 60 * $ns_per_sec"
let "ns_per_hour = 60 * $ns_per_min"
let "ns_per_day = 24 * $ns_per_hour"
if [ $1 -ge ${ns_per_day} ]; then
  echo -n "$(($1 / ${ns_per_day}))d"
fi
if [ $1 -ge ${ns_per_hour} ]; then
  printf '%02dh' $((($1 % ${ns_per_day}) / ${ns_per_hour}))
fi
if [ $1 -ge ${ns_per_min} ]; then
  printf '%02dm' $((($1 % ${ns_per_hour}) / ${ns_per_min}))
fi
printf '%02d.%09ds\n' $((($1 % ${ns_per_min}) / ${ns_per_sec})) $(($1 % ${ns_per_sec}))
