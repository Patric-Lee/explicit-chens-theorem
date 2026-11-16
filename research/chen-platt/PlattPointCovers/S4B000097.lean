import PlattPointSubsetKernel
import PlattPointPackets.S1B000113
import PlattPointPackets.S1B000114
import PlattGlobalGrid.S4B000097
namespace ChenEffective.PlattWindow.PointCovers.S4B000097
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000113.points ++ ChenEffective.PlattWindow.PointPackets.S1B000114.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S4B000097.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S4B000097.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S4B000097
