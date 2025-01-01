
dune exec --root extraction -- ./generate_circuits.exe
dune exec --root extraction -- ./PQASM.exe
echo "Executed hamming"
mv *.qasm vqo_files
echo "Running VOQC optimizations on generated circuits..."
dune exec --root extraction -- ./run_voqc.exe > /dev/null