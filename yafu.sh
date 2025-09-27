#!/bin/bash
set -u
let "minute_ns = 60 * 1000 * 1000 * 1000"
let "hour_ns = 60 * ${minute_ns}"
#	if [ ${origstart} == -1 ]; then
#		start="$(($RANDOM * 3))"
#	fi
declare num
while read num; do
  exec 9>/tmp/factordb-composites/${num}
  if flock -xn 9; then
      declare factor
      start_time="$(date -Is)"
      echo "${start_time}: Factoring ${num}"
      while read -r factor; do
        now="$(date -Is)"
        echo "${now}: Found factor ${factor} of ${num}"
        output=$(sem --id 'factordb-curl' --fg -j 2 curl -X POST --retry 10 --retry-all-errors --retry-delay 10 http://factordb.com/reportfactor.php -d "number=${num}&factor=${factor}")
        error=$?
        grep -q "submitted" <<< "$output"
        if [ $? -ne 0 ]; then
          error=1
        fi
        if [ $error -ne 0 ]; then
          echo "${now}: Error submitting factor ${factor} of ${num}: ${output}"
          flock failed-submissions.csv -c "echo \"${now}\",${num},${factor} >> ${main_working_dir}/failed-submissions.csv"
        else
          echo "\"${now}\",${num},${factor}" >> "${main_working_dir}/factor-submissions.csv"
          grep -q "Already" <<< "$output"
          if [ $? -eq 0 ]; then
            echo "${id}: Factor ${factor} of ${num} already known! Aborting batch after ${factors_so_far} factors and ${composites_so_far} composites."
            exit 0
          else
            echo "${id}: Submitting factor ${factor}: $output"
            echo "${id}: Factor ${factor} of ${num} accepted."
          fi
        fi
      done < <(
        cd "/tmp/${id}"
        factored=0
        for (( try=0 ; try<3 ; try++ )); do
          echo "${id}: $(date -Is): Factoring ${num} with yafu" >&2
          yafu -threads 1 -R -qssave "./qs" -session "./session" -logfile "./log" -o "./nfs" <<<"factor(${num})" 2>&1 \
            | tee "./out" \
            | grep '\(^P[0-9]\|factor = \)' | grep -o '= [0-9]\+' | grep -o '[0-9]\+' \
            | head -n -1 | uniq
          grep -q '^P[0-9]' "./out"
          if [ $? -eq 0 ]; then
            end_time=$(date +%s%N)
            echo "${id}: $(date -Is): Done factoring ${num} with yafu after $(format-nanos.sh $(($end_time - $start_time)))" >&2
            factored=1
            break
          else
            tail "./out" >&2
          fi
        done
        if [ $factored -eq 0 ]; then
          echo "${id}: $(date -Is): Factoring ${num} with msieve" >&2
          msieve -e -q -s "/tmp/msieve_${num}.dat" -t "${threads}" "${num}" | grep -o ':[0-9 ]\+' | grep -o '[0-9]\+' | head -n -1 | uniq
          end_time=$(date +%s%N)
          echo "${id}: $(date -Is): Done factoring ${num} with msieve after $(format-nanos.sh $(($end_time - $start_time)))" >&2
        fi
      )
  else
    echo "${id}: Skipping ${num} because it's already being factored"
  fi
done
