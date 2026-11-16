import PlattLogKernel
namespace ChenEffective.PlattWindow.LogCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option trace.profiler true
set_option trace.profiler.threshold 10
theorem arithmetic_bench_1 :
    [
    (Nat.beq (rationalBounds 9999935488 1 33).1 6481199038390416 &&
     Nat.beq (rationalBounds 9999935488 1 33).2 6481199038391538 &&
     Nat.beq (rationalBounds 6481199038390416 scale 4).1 882879269665140 &&
     Nat.beq (rationalBounds 6481199038391538 scale 4).2 882879269665353)].all (fun b => b) = true := by
  decide +kernel
#print axioms arithmetic_bench_1
end ChenEffective.PlattWindow.LogCertificate
