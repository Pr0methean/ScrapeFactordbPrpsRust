#!/bin/bash
set -u
#	if [ ${origstart} == -1 ]; then
#		start="$(($RANDOM * 3))"
#	fi
mkdir /tmp/factordb-composites
declare num
while read -r num; do
  exec 9>"/tmp/factordb-composites/${num}"
  if flock -xn 9; then
      declare factor
      start_time="$(date -Is)"
      while read -r factor; do
        now="$(date -Is)"
        echo "${now}: Found factor ${factor} of ${num}"
        output=$(sem --id 'factordb-curl' --fg -j 2 curl -X POST --retry 10 --retry-all-errors --retry-delay 10 http://factordb.com/reportfactor.php -d "number=${num}&factor=${factor}")
        error=$?
        if ! grep -q "submitted" <<< "$output"; then
          error=1
        fi
        if [ $error -ne 0 ]; then
          echo "${now}: Error submitting factor ${factor} of ${num}: ${output}"
          flock failed-submissions.csv -c "echo \"${now}\",${num},${factor} >> failed-submissions.csv"
        else
          echo "\"${now}\",${num},${factor}" >> "factor-submissions.csv"
          if grep -q "Already" <<< "$output"; then
            echo "Factor ${factor} of ${num} already known!"
          else
            echo "Factor ${factor} of ${num} accepted: ${output}"
          fi
        fi
      done < <(
        echo "$(date -Is): Factoring ${num} with yafu" >&2
        ./yafu -threads 1 -R -qssave "./qs" -session "./session" -logfile "./log" -o "./nfs" <<<"factor(${num})" 2>&1 \
          | tee "./out" \
          | grep '\(^P[0-9]\|factor = \)' | grep -o '= [0-9]\+' | grep -o '[0-9]\+' \
          | head -n -1 | uniq
        if grep -q '^P[0-9]' "./out"; then
          end_time=$(date +%s%N)
          echo "$(date -Is): Done factoring ${num} with yafu after $(format-nanos.sh $((end_time - start_time)))" >&2
        else
          echo "$(date -Is): Failed to factor ${num} with yafu" >&2
          tail "./out" >&2
        fi
        rm ".out"
      )
  else
    echo "Skipping ${num} because it's already being factored"
  fi
done
