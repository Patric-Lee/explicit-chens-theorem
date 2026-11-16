import PlattPointSubsetKernel
import PlattPointPackets.S1B000102
import PlattPointPackets.S1B000103
import PlattGlobalGrid.S4B000081
namespace ChenEffective.PlattWindow.PointCovers.S4B000081
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000102.points ++ ChenEffective.PlattWindow.PointPackets.S1B000103.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S4B000081.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S4B000081.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S4B000081
