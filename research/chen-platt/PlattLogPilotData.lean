import PlattLogKernel
namespace ChenEffective.PlattWindow.LogCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem pilot_log_arithmetic :
    (Nat.beq (rationalBounds 9999935488 1 33).1 6481199038390416 &&
     Nat.beq (rationalBounds 9999935488 1 33).2 6481199038391538 &&
     Nat.beq (rationalBounds 6481199038390416 scale 4).1 882879269665140 &&
     Nat.beq (rationalBounds 6481199038391538 scale 4).2 882879269665353) = true := by
  decide +kernel
#print axioms pilot_log_arithmetic
end ChenEffective.PlattWindow.LogCertificate
