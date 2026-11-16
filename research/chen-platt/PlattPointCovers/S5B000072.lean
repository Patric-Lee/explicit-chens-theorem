import PlattPointSubsetKernel
import PlattPointPackets.S1B000216
import PlattPointPackets.S1B000217
import PlattPointPackets.S1B000218
import PlattGlobalGrid.S5B000072
namespace ChenEffective.PlattWindow.PointCovers.S5B000072
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000216.points ++ ChenEffective.PlattWindow.PointPackets.S1B000217.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000218.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000072.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000072.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000072
