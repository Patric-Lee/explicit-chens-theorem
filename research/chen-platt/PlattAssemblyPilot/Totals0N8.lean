import PlattIncrementKernel
import PlattCertificates.Count131072.C000000
import PlattCertificates.Count131072.C000001
import PlattCertificates.Count131072.C000002
import PlattCertificates.Count131072.C000003
import PlattCertificates.Count131072.C000004
import PlattCertificates.Count131072.C000005
import PlattCertificates.Count131072.C000006
import PlattCertificates.Count131072.C000007
namespace ChenEffective.PlattWindow.AssemblyPilot.Totals0N8
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨4000000,4131072,598080220703,598084933579⟩
theorem certified0 : IncrementCertified row0 :=
 certifyIncrement 4000001 4 4096 Manual.Count131072.C000000.packed 598080220703 598084933579
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 Manual.Count131072.C000000.count_checked Manual.Count131072.C000000.arithmetic_checked
def row1 : IncrementRow := ⟨4131072,4194304,281556403798,281558570197⟩
theorem certified1 : IncrementCertified row1 :=
 certifyIncrement 4131073 4 1976 Manual.Count131072.C000001.packed 281556403798 281558570197
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 Manual.Count131072.C000001.count_checked Manual.Count131072.C000001.arithmetic_checked
def row2 : IncrementRow := ⟨4194304,4325376,563436548591,563445017565⟩
theorem certified2 : IncrementCertified row2 :=
 certifyIncrement 4194305 5 2048 Manual.Count131072.C000002.packed 563436548591 563445017565
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 Manual.Count131072.C000002.count_checked Manual.Count131072.C000002.arithmetic_checked
def row3 : IncrementRow := ⟨4325376,4456448,552068910285,552076959834⟩
theorem certified3 : IncrementCertified row3 :=
 certifyIncrement 4325377 5 2048 Manual.Count131072.C000003.packed 552068910285 552076959834
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 Manual.Count131072.C000003.count_checked Manual.Count131072.C000003.arithmetic_checked
def row4 : IncrementRow := ⟨4456448,4587520,532182173660,532189708963⟩
theorem certified4 : IncrementCertified row4 :=
 certifyIncrement 4456449 5 2048 Manual.Count131072.C000004.packed 532182173660 532189708963
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 Manual.Count131072.C000004.count_checked Manual.Count131072.C000004.arithmetic_checked
def row5 : IncrementRow := ⟨4587520,4718592,516808052010,516815163302⟩
theorem certified5 : IncrementCertified row5 :=
 certifyIncrement 4587521 5 2048 Manual.Count131072.C000005.packed 516808052010 516815163302
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 Manual.Count131072.C000005.count_checked Manual.Count131072.C000005.arithmetic_checked
def row6 : IncrementRow := ⟨4718592,4849664,500120888322,500127581581⟩
theorem certified6 : IncrementCertified row6 :=
 certifyIncrement 4718593 5 2048 Manual.Count131072.C000006.packed 500120888322 500127581581
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 Manual.Count131072.C000006.count_checked Manual.Count131072.C000006.arithmetic_checked
def row7 : IncrementRow := ⟨4849664,4980736,491480357459,491486759727⟩
theorem certified7 : IncrementCertified row7 :=
 certifyIncrement 4849665 5 2048 Manual.Count131072.C000007.packed 491480357459 491486759727
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 Manual.Count131072.C000007.count_checked Manual.Count131072.C000007.arithmetic_checked
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows :=
 CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem summary_checked : checkIncrementSummary 4000000 4980736 4035733554828 4035784694748 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.AssemblyPilot.Totals0N8

-- Bounded resource measurement run.
