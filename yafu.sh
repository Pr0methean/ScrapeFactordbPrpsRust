#!/bin/bash
set -u
#	if [ ${origstart} == -1 ]; then
#		start="$(($RANDOM * 3))"
#	fi
mkdir /tmp/factordb-composites
declare num
while read -r num; do
  if [ ! -f "./yafu" ]; then
    echo "Aborting because yafu has been deleted"
    exit 0
  fi
  exec 9>"/tmp/factordb-composites/${num}"
  if flock -xn 9; then
      let real_digits="${#num}"
      let "max_factor_digits = real_digits / 2 + 2"
      declare factor
      start_time="$(date +%s%N)"
      while read -r factor; do (
        echo "Found factor ${factor} of ${num}"
        output=$(curl -X POST --retry 10 --retry-all-errors --retry-delay 10 https://factordb.com/reportfactor.php -d "number=${num}&factor=${factor}")
        error=$?
        if ! grep -q "submitted" <<< "$output"; then
          error=1
        fi
        if [ $error -ne 0 ]; then
          echo "Error submitting factor ${factor} of ${num}: ${output}"
          flock failed-submissions.csv -c "echo \"$(date -Is)\",${num},${factor} >> failed-submissions.csv"
        else
          if grep -q "Already" <<< "$output"; then
            echo "Factor ${factor} of ${num} already known!"
          else
            echo "Factor ${factor} of ${num} accepted: ${output}"
          fi
        fi
      )& done < <(
        echo "Factoring ${num} with yafu" >&2
        ./yafu -threads 2 -R -qssave "./qs" -session "./session" -logfile "./log" -o "./nfs" -pscreen <<<"factor(${num})" 2>&1 \
          | tee "./out" \
          | grep -i '\(P[0-9]\+\|factor\) = ' | grep -o '= [0-9]\+' | grep -o '[0-9]\+' | grep -o "^[0-9]\{1,$max_factor_digits\}$" \
          | awk '!x[$0]++'
        if grep -q '^P[0-9]' "./out"; then
          end_time=$(date +%s%N)
          echo "Done factoring ${num} with yafu after $(./format-nanos.sh $((end_time - start_time)))" >&2
        else
          echo "Failed to factor ${num} with yafu" >&2
          tail "./out" >&2
        fi
        rm "./out"
      )
  else
    echo "Skipping ${num} because it's already being factored"
  fi
done
