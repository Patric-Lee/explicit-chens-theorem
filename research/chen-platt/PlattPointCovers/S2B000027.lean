import PlattPointSubsetKernel
import PlattPointPackets.S1B000020
import PlattPointPackets.S1B000021
import PlattGlobalGrid.S2B000027
namespace ChenEffective.PlattWindow.PointCovers.S2B000027
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000020.points ++ ChenEffective.PlattWindow.PointPackets.S1B000021.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S2B000027.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S2B000027.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S2B000027
