make
make

OK = 0

./aeff.exe ./tests/dummy.aeff
((OK = OK + $?))
./aeff.exe ./tests/function.aeff
((OK = OK + $?))
./aeff.exe ./tests/list.aeff
((OK = OK + $?))

./aeff.exe ./examples/async.aeff
((OK = OK + $?))
./aeff.exe ./examples/cancellableCall.aeff
((OK = OK + $?))
# ./aeff.exe ./examples/feed.aeff
# ((OK = OK + $?))
./aeff.exe ./examples/heapPure.aeff
((OK = OK + $?))
./aeff.exe ./examples/heapRef.aeff
((OK = OK + $?))
./aeff.exe ./examples/preemptive.aeff
((OK = OK + $?))
./aeff.exe ./examples/process_with.aeff
((OK = OK + $?))
./aeff.exe ./examples/remoteCall.aeff
((OK = OK + $?))
./aeff.exe ./examples/runner.aeff
((OK = OK + $?))
./aeff.exe ./examples/select.aeff
((OK = OK + $?))
./aeff.exe ./examples/ticktock.aeff
((OK = OK + $?))

echo
echo "script exit code = " $OK
