#!/bin/bash

PID=$(dotnet trace ps | grep -m 1 liyh | awk '{print $1}')

echo "Liyh PID: $PID."

TRACE_FILE="./ignore/trace/liyh_trace_${PID}"
dotnet trace collect --format Speedscope -p $PID -o $TRACE_FILE
wait $!

speedscope $TRACE_FILE.speedscope.json
wait $!

